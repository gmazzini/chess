#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <math.h>
#include <pthread.h>

#define MAX_MOVES 256
#define SEARCH_DEPTH 4
#define ROOT_THREADS 6
#define ROOT_THREADS_MAX 64
#define INF 1000000000

#define FLAG_NONE 0
#define FLAG_CAPTURE 1
#define FLAG_EP 2
#define FLAG_CASTLE 4
#define FLAG_PROMO 8

typedef struct {
  char b[64];
  int side;
  int castle;
  int ep;
  int halfmove;
  int fullmove;
} Pos;

typedef struct {
  int from;
  int to;
  char promo;
  int flags;
} Move;

typedef struct {
  double value;
  double complexity;
  double risk;
  double forcing;
  double stability;
  double hanging;
  double tactic;
  double opening;
  double score;
} Metrics;

typedef struct {
  double value;
  double complexity;
  double risk;
  double forcing;
  double stability;
  double hanging;
  double tactic;
  double coherence;
  double resilience;
  double activity;
  double future;
} Phi;

static double signed_forcing(double value,double forcing);
static double state_activity(const Pos *p,int perspective);
static double state_transfer(const Pos *p,int perspective);
static double state_future_options(const Pos *p,int perspective);

static int file_of(int sq){ return sq & 7; }
static int rank_of(int sq){ return sq >> 3; }
static int in_board(int f,int r){ return f>=0 && f<8 && r>=0 && r<8; }
static int sq_of(int f,int r){ return r*8+f; }
static int is_white_piece(char p){ return p>='A' && p<='Z'; }
static int is_black_piece(char p){ return p>='a' && p<='z'; }
static int piece_side(char p){ if(is_white_piece(p)) return 0; if(is_black_piece(p)) return 1; return -1; }
static char lower_piece(char p){ return (char)tolower((unsigned char)p); }

static int piece_value(char p){
  p=lower_piece(p);
  if(p=='p') return 100;
  if(p=='n') return 320;
  if(p=='b') return 330;
  if(p=='r') return 500;
  if(p=='q') return 900;
  if(p=='k') return 0;
  return 0;
}

static int parse_square(const char *s){
  int f,r;
  if(s[0]<'a' || s[0]>'h' || s[1]<'1' || s[1]>'8') return -1;
  f=s[0]-'a';
  r=s[1]-'1';
  return sq_of(f,r);
}

static void square_name(int sq,char out[3]){
  out[0]=(char)('a'+file_of(sq));
  out[1]=(char)('1'+rank_of(sq));
  out[2]=0;
}

static int parse_fen(const char *fen,Pos *p){
  int i,idx,r,f,n;
  char side[8],castle[16],ep[8];
  const char *q;

  memset(p,0,sizeof(Pos));
  for(i=0;i<64;i++) p->b[i]='.';
  p->ep=-1;
  p->halfmove=0;
  p->fullmove=1;

  q=fen;
  r=7;
  f=0;
  while(*q && *q!=' '){
    if(*q=='/'){
      if(f!=8) return 0;
      r--;
      f=0;
      q++;
      continue;
    }
    if(isdigit((unsigned char)*q)){
      n=*q-'0';
      if(n<1 || n>8 || f+n>8) return 0;
      f+=n;
      q++;
      continue;
    }
    if(strchr("PNBRQKpnbrqk",*q)!=NULL){
      if(!in_board(f,r)) return 0;
      p->b[sq_of(f,r)]=*q;
      f++;
      q++;
      continue;
    }
    return 0;
  }
  if(r!=0 || f!=8) return 0;
  while(*q==' ') q++;
  idx=0;
  while(*q && *q!=' ' && idx<7) side[idx++]=*q++;
  side[idx]=0;
  while(*q==' ') q++;
  idx=0;
  while(*q && *q!=' ' && idx<15) castle[idx++]=*q++;
  castle[idx]=0;
  while(*q==' ') q++;
  idx=0;
  while(*q && *q!=' ' && idx<7) ep[idx++]=*q++;
  ep[idx]=0;
  while(*q==' ') q++;
  if(*q) p->halfmove=atoi(q);
  while(*q && *q!=' ') q++;
  while(*q==' ') q++;
  if(*q) p->fullmove=atoi(q);

  if(strcmp(side,"w")==0) p->side=0;
  else if(strcmp(side,"b")==0) p->side=1;
  else return 0;

  p->castle=0;
  if(strchr(castle,'K')) p->castle|=1;
  if(strchr(castle,'Q')) p->castle|=2;
  if(strchr(castle,'k')) p->castle|=4;
  if(strchr(castle,'q')) p->castle|=8;

  if(strcmp(ep,"-")==0) p->ep=-1;
  else p->ep=parse_square(ep);

  return 1;
}

static void add_move(Move *moves,int *n,int from,int to,char promo,int flags){
  if(*n>=MAX_MOVES) return;
  moves[*n].from=from;
  moves[*n].to=to;
  moves[*n].promo=promo;
  moves[*n].flags=flags;
  (*n)++;
}

static int find_king(const Pos *p,int side){
  int i;
  char k;
  k=side==0?'K':'k';
  for(i=0;i<64;i++) if(p->b[i]==k) return i;
  return -1;
}

static int attacked_by(const Pos *p,int sq,int side){
  int f,r,tf,tr,i,j,s;
  char pc;
  int knight[8][2]={{1,2},{2,1},{2,-1},{1,-2},{-1,-2},{-2,-1},{-2,1},{-1,2}};
  int bishop[4][2]={{1,1},{1,-1},{-1,1},{-1,-1}};
  int rook[4][2]={{1,0},{-1,0},{0,1},{0,-1}};
  int king[8][2]={{1,1},{1,0},{1,-1},{0,1},{0,-1},{-1,1},{-1,0},{-1,-1}};

  f=file_of(sq);
  r=rank_of(sq);

  if(side==0){
    tr=r-1;
    if(tr>=0){
      tf=f-1;
      if(tf>=0 && p->b[sq_of(tf,tr)]=='P') return 1;
      tf=f+1;
      if(tf<8 && p->b[sq_of(tf,tr)]=='P') return 1;
    }
  } else {
    tr=r+1;
    if(tr<8){
      tf=f-1;
      if(tf>=0 && p->b[sq_of(tf,tr)]=='p') return 1;
      tf=f+1;
      if(tf<8 && p->b[sq_of(tf,tr)]=='p') return 1;
    }
  }

  for(i=0;i<8;i++){
    tf=f+knight[i][0]; tr=r+knight[i][1];
    if(in_board(tf,tr)){
      pc=p->b[sq_of(tf,tr)];
      if(side==0 && pc=='N') return 1;
      if(side==1 && pc=='n') return 1;
    }
  }

  for(i=0;i<4;i++){
    tf=f+bishop[i][0]; tr=r+bishop[i][1];
    while(in_board(tf,tr)){
      pc=p->b[sq_of(tf,tr)];
      if(pc!='.'){
        if(piece_side(pc)==side && (lower_piece(pc)=='b' || lower_piece(pc)=='q')) return 1;
        break;
      }
      tf+=bishop[i][0]; tr+=bishop[i][1];
    }
  }

  for(i=0;i<4;i++){
    tf=f+rook[i][0]; tr=r+rook[i][1];
    while(in_board(tf,tr)){
      pc=p->b[sq_of(tf,tr)];
      if(pc!='.'){
        if(piece_side(pc)==side && (lower_piece(pc)=='r' || lower_piece(pc)=='q')) return 1;
        break;
      }
      tf+=rook[i][0]; tr+=rook[i][1];
    }
  }

  for(j=0;j<8;j++){
    tf=f+king[j][0]; tr=r+king[j][1];
    if(in_board(tf,tr)){
      pc=p->b[sq_of(tf,tr)];
      if(side==0 && pc=='K') return 1;
      if(side==1 && pc=='k') return 1;
    }
  }
  (void)s;
  return 0;
}

static int lowest_attacker_value(const Pos *p,int sq,int side){
  int f,r,tf,tr,i,j,best,s;
  char pc;
  int knight[8][2]={{1,2},{2,1},{2,-1},{1,-2},{-1,-2},{-2,-1},{-2,1},{-1,2}};
  int bishop[4][2]={{1,1},{1,-1},{-1,1},{-1,-1}};
  int rook[4][2]={{1,0},{-1,0},{0,1},{0,-1}};
  int king[8][2]={{1,1},{1,0},{1,-1},{0,1},{0,-1},{-1,1},{-1,0},{-1,-1}};

  best=INF;
  f=file_of(sq);
  r=rank_of(sq);

  if(side==0){
    tr=r-1;
    if(tr>=0){
      tf=f-1;
      if(tf>=0 && p->b[sq_of(tf,tr)]=='P') best=100;
      tf=f+1;
      if(tf<8 && p->b[sq_of(tf,tr)]=='P') best=100;
    }
  } else {
    tr=r+1;
    if(tr<8){
      tf=f-1;
      if(tf>=0 && p->b[sq_of(tf,tr)]=='p') best=100;
      tf=f+1;
      if(tf<8 && p->b[sq_of(tf,tr)]=='p') best=100;
    }
  }

  for(i=0;i<8;i++){
    tf=f+knight[i][0]; tr=r+knight[i][1];
    if(in_board(tf,tr)){
      pc=p->b[sq_of(tf,tr)];
      if(piece_side(pc)==side && lower_piece(pc)=='n' && 320<best) best=320;
    }
  }

  for(i=0;i<4;i++){
    tf=f+bishop[i][0]; tr=r+bishop[i][1];
    while(in_board(tf,tr)){
      s=sq_of(tf,tr);
      pc=p->b[s];
      if(pc!='.'){
        if(piece_side(pc)==side && (lower_piece(pc)=='b' || lower_piece(pc)=='q')){
          j=piece_value(pc);
          if(j<best) best=j;
        }
        break;
      }
      tf+=bishop[i][0]; tr+=bishop[i][1];
    }
  }

  for(i=0;i<4;i++){
    tf=f+rook[i][0]; tr=r+rook[i][1];
    while(in_board(tf,tr)){
      s=sq_of(tf,tr);
      pc=p->b[s];
      if(pc!='.'){
        if(piece_side(pc)==side && (lower_piece(pc)=='r' || lower_piece(pc)=='q')){
          j=piece_value(pc);
          if(j<best) best=j;
        }
        break;
      }
      tf+=rook[i][0]; tr+=rook[i][1];
    }
  }

  for(i=0;i<8;i++){
    tf=f+king[i][0]; tr=r+king[i][1];
    if(in_board(tf,tr)){
      pc=p->b[sq_of(tf,tr)];
      if(piece_side(pc)==side && lower_piece(pc)=='k' && 10000<best) best=10000;
    }
  }

  if(best==INF) return 0;
  return best;
}

static int in_check(const Pos *p,int side){
  int k;
  k=find_king(p,side);
  if(k<0) return 1;
  return attacked_by(p,k,1-side);
}

static void make_move(const Pos *p,const Move *m,Pos *q){
  char pc,captured,newpc;
  int from,to,side;

  *q=*p;
  from=m->from;
  to=m->to;
  pc=q->b[from];
  captured=q->b[to];
  side=p->side;

  q->b[from]='.';
  if(m->flags & FLAG_EP){
    if(side==0) q->b[to-8]='.';
    else q->b[to+8]='.';
  }

  newpc=pc;
  if(m->flags & FLAG_PROMO){
    newpc=m->promo;
    if(side==1) newpc=(char)tolower((unsigned char)newpc);
  }
  q->b[to]=newpc;

  if(m->flags & FLAG_CASTLE){
    if(to==sq_of(6,0)){
      q->b[sq_of(5,0)]='R'; q->b[sq_of(7,0)]='.';
    } else if(to==sq_of(2,0)){
      q->b[sq_of(3,0)]='R'; q->b[sq_of(0,0)]='.';
    } else if(to==sq_of(6,7)){
      q->b[sq_of(5,7)]='r'; q->b[sq_of(7,7)]='.';
    } else if(to==sq_of(2,7)){
      q->b[sq_of(3,7)]='r'; q->b[sq_of(0,7)]='.';
    }
  }

  if(pc=='K') q->castle&=~3;
  if(pc=='k') q->castle&=~12;
  if(from==sq_of(0,0) || to==sq_of(0,0) || captured=='R') q->castle&=~2;
  if(from==sq_of(7,0) || to==sq_of(7,0) || captured=='R') q->castle&=~1;
  if(from==sq_of(0,7) || to==sq_of(0,7) || captured=='r') q->castle&=~8;
  if(from==sq_of(7,7) || to==sq_of(7,7) || captured=='r') q->castle&=~4;

  q->ep=-1;
  if(lower_piece(pc)=='p'){
    if(side==0 && rank_of(from)==1 && rank_of(to)==3) q->ep=from+8;
    if(side==1 && rank_of(from)==6 && rank_of(to)==4) q->ep=from-8;
  }

  if(lower_piece(pc)=='p' || captured!='.' || (m->flags & FLAG_EP)) q->halfmove=0;
  else q->halfmove++;
  if(side==1) q->fullmove++;
  q->side=1-side;
}

static void gen_pseudo(const Pos *p,Move *moves,int *n){
  int i,side,f,r,dir,start_rank,promo_rank,to,to2,tf,tr,j;
  char pc,target;
  int knight[8][2]={{1,2},{2,1},{2,-1},{1,-2},{-1,-2},{-2,-1},{-2,1},{-1,2}};
  int bishop[4][2]={{1,1},{1,-1},{-1,1},{-1,-1}};
  int rook[4][2]={{1,0},{-1,0},{0,1},{0,-1}};
  int kingd[8][2]={{1,1},{1,0},{1,-1},{0,1},{0,-1},{-1,1},{-1,0},{-1,-1}};

  *n=0;
  side=p->side;
  for(i=0;i<64;i++){
    pc=p->b[i];
    if(pc=='.' || piece_side(pc)!=side) continue;
    f=file_of(i);
    r=rank_of(i);
    if(lower_piece(pc)=='p'){
      dir=side==0?1:-1;
      start_rank=side==0?1:6;
      promo_rank=side==0?6:1;
      tr=r+dir;
      if(in_board(f,tr)){
        to=sq_of(f,tr);
        if(p->b[to]=='.'){
          if(r==promo_rank){
            add_move(moves,n,i,to,'Q',FLAG_PROMO);
            add_move(moves,n,i,to,'R',FLAG_PROMO);
            add_move(moves,n,i,to,'B',FLAG_PROMO);
            add_move(moves,n,i,to,'N',FLAG_PROMO);
          } else {
            add_move(moves,n,i,to,0,0);
          }
          if(r==start_rank){
            to2=sq_of(f,r+2*dir);
            if(p->b[to2]=='.') add_move(moves,n,i,to2,0,0);
          }
        }
      }
      for(j=-1;j<=1;j+=2){
        tf=f+j; tr=r+dir;
        if(!in_board(tf,tr)) continue;
        to=sq_of(tf,tr);
        target=p->b[to];
        if(target!='.' && piece_side(target)==1-side){
          if(r==promo_rank){
            add_move(moves,n,i,to,'Q',FLAG_CAPTURE|FLAG_PROMO);
            add_move(moves,n,i,to,'R',FLAG_CAPTURE|FLAG_PROMO);
            add_move(moves,n,i,to,'B',FLAG_CAPTURE|FLAG_PROMO);
            add_move(moves,n,i,to,'N',FLAG_CAPTURE|FLAG_PROMO);
          } else {
            add_move(moves,n,i,to,0,FLAG_CAPTURE);
          }
        }
        if(to==p->ep) add_move(moves,n,i,to,0,FLAG_EP|FLAG_CAPTURE);
      }
    } else if(lower_piece(pc)=='n'){
      for(j=0;j<8;j++){
        tf=f+knight[j][0]; tr=r+knight[j][1];
        if(!in_board(tf,tr)) continue;
        to=sq_of(tf,tr); target=p->b[to];
        if(target=='.') add_move(moves,n,i,to,0,0);
        else if(piece_side(target)==1-side) add_move(moves,n,i,to,0,FLAG_CAPTURE);
      }
    } else if(lower_piece(pc)=='b' || lower_piece(pc)=='r' || lower_piece(pc)=='q'){
      int dirs[8][2];
      int nd;
      nd=0;
      if(lower_piece(pc)=='b' || lower_piece(pc)=='q'){
        for(j=0;j<4;j++){ dirs[nd][0]=bishop[j][0]; dirs[nd][1]=bishop[j][1]; nd++; }
      }
      if(lower_piece(pc)=='r' || lower_piece(pc)=='q'){
        for(j=0;j<4;j++){ dirs[nd][0]=rook[j][0]; dirs[nd][1]=rook[j][1]; nd++; }
      }
      for(j=0;j<nd;j++){
        tf=f+dirs[j][0]; tr=r+dirs[j][1];
        while(in_board(tf,tr)){
          to=sq_of(tf,tr); target=p->b[to];
          if(target=='.') add_move(moves,n,i,to,0,0);
          else {
            if(piece_side(target)==1-side) add_move(moves,n,i,to,0,FLAG_CAPTURE);
            break;
          }
          tf+=dirs[j][0]; tr+=dirs[j][1];
        }
      }
    } else if(lower_piece(pc)=='k'){
      for(j=0;j<8;j++){
        tf=f+kingd[j][0]; tr=r+kingd[j][1];
        if(!in_board(tf,tr)) continue;
        to=sq_of(tf,tr); target=p->b[to];
        if(target=='.') add_move(moves,n,i,to,0,0);
        else if(piece_side(target)==1-side) add_move(moves,n,i,to,0,FLAG_CAPTURE);
      }
      if(side==0 && i==sq_of(4,0) && !in_check(p,0)){
        if((p->castle&1) && p->b[sq_of(5,0)]=='.' && p->b[sq_of(6,0)]=='.' && !attacked_by(p,sq_of(5,0),1) && !attacked_by(p,sq_of(6,0),1)) add_move(moves,n,i,sq_of(6,0),0,FLAG_CASTLE);
        if((p->castle&2) && p->b[sq_of(3,0)]=='.' && p->b[sq_of(2,0)]=='.' && p->b[sq_of(1,0)]=='.' && !attacked_by(p,sq_of(3,0),1) && !attacked_by(p,sq_of(2,0),1)) add_move(moves,n,i,sq_of(2,0),0,FLAG_CASTLE);
      }
      if(side==1 && i==sq_of(4,7) && !in_check(p,1)){
        if((p->castle&4) && p->b[sq_of(5,7)]=='.' && p->b[sq_of(6,7)]=='.' && !attacked_by(p,sq_of(5,7),0) && !attacked_by(p,sq_of(6,7),0)) add_move(moves,n,i,sq_of(6,7),0,FLAG_CASTLE);
        if((p->castle&8) && p->b[sq_of(3,7)]=='.' && p->b[sq_of(2,7)]=='.' && p->b[sq_of(1,7)]=='.' && !attacked_by(p,sq_of(3,7),0) && !attacked_by(p,sq_of(2,7),0)) add_move(moves,n,i,sq_of(2,7),0,FLAG_CASTLE);
      }
    }
  }
}

static void gen_legal(const Pos *p,Move *legal,int *ln){
  Move pseudo[MAX_MOVES];
  Pos q;
  int pn,i,side;
  side=p->side;
  gen_pseudo(p,pseudo,&pn);
  *ln=0;
  for(i=0;i<pn;i++){
    make_move(p,&pseudo[i],&q);
    if(!in_check(&q,side)){
      if(*ln<MAX_MOVES){ legal[*ln]=pseudo[i]; (*ln)++; }
    }
  }
}

static int material_eval(const Pos *p,int perspective){
  int i,score,side,val;
  score=0;
  for(i=0;i<64;i++){
    side=piece_side(p->b[i]);
    if(side<0) continue;
    val=piece_value(p->b[i]);
    if(side==perspective) score+=val;
    else score-=val;
  }
  return score;
}

static int center_eval(const Pos *p,int perspective){
  int sqs[4];
  int i,sq,score;
  char pc;
  sqs[0]=sq_of(3,3); sqs[1]=sq_of(4,3); sqs[2]=sq_of(3,4); sqs[3]=sq_of(4,4);
  score=0;
  for(i=0;i<4;i++){
    sq=sqs[i]; pc=p->b[sq];
    if(pc!='.'){
      if(piece_side(pc)==perspective) score+=20;
      else score-=20;
    }
    if(attacked_by(p,sq,perspective)) score+=8;
    if(attacked_by(p,sq,1-perspective)) score-=8;
  }
  return score;
}

static int king_safety_eval(const Pos *p,int perspective){
  int k,f,r,df,dr,tf,tr,sq,score;
  k=find_king(p,perspective);
  if(k<0) return -500;
  f=file_of(k); r=rank_of(k); score=0;
  for(df=-1;df<=1;df++){
    for(dr=-1;dr<=1;dr++){
      if(df==0 && dr==0) continue;
      tf=f+df; tr=r+dr;
      if(!in_board(tf,tr)) continue;
      sq=sq_of(tf,tr);
      if(attacked_by(p,sq,1-perspective)) score-=12;
      if(attacked_by(p,sq,perspective)) score+=3;
    }
  }
  if(in_check(p,perspective)) score-=80;
  if(in_check(p,1-perspective)) score+=50;
  return score;
}

static int mobility_for_side(Pos *p,int side){
  Move m[MAX_MOVES];
  int n,old;
  old=p->side;
  p->side=side;
  gen_pseudo(p,m,&n);
  p->side=old;
  return n;
}

static int static_eval(const Pos *p,int perspective){
  Pos q;
  int mymob,opmob,score;
  q=*p;
  mymob=mobility_for_side(&q,perspective);
  opmob=mobility_for_side(&q,1-perspective);
  score=material_eval(p,perspective);
  score+=4*(mymob-opmob);
  score+=center_eval(p,perspective);
  score+=king_safety_eval(p,perspective);
  return score;
}

static double move_forcing(const Pos *after,int perspective){
  Move replies[MAX_MOVES];
  int n;
  Pos q;
  q=*after;
  gen_legal(&q,replies,&n);
  if(in_check(after,1-perspective)) return 1.0 + (30.0-n)/30.0;
  if(n<=0) return 2.0;
  return (30.0-n)/30.0;
}

static double move_complexity(const Pos *after){
  Move replies[MAX_MOVES];
  int n;
  Pos q;
  q=*after;
  gen_legal(&q,replies,&n);
  if(n<0) n=0;
  return (double)n/40.0;
}

static double move_risk(const Pos *after,int perspective){
  int k,enemy_attacks,own_attacks,i;
  double risk;
  k=find_king(after,perspective);
  enemy_attacks=0;
  own_attacks=0;
  for(i=0;i<64;i++){
    if(attacked_by(after,i,1-perspective)) enemy_attacks++;
    if(attacked_by(after,i,perspective)) own_attacks++;
  }
  risk=0.0;
  if(k>=0 && attacked_by(after,k,1-perspective)) risk+=2.0;
  risk+=(double)(enemy_attacks-own_attacks)/64.0;
  return risk;
}

static double hanging_penalty(const Pos *after,int perspective){
  int i,enemy,val,attacker,defended;
  char pc,lp;
  double penalty;

  enemy=1-perspective;
  penalty=0.0;
  for(i=0;i<64;i++){
    pc=after->b[i];
    if(pc=='.' || piece_side(pc)!=perspective) continue;
    lp=lower_piece(pc);
    if(lp=='k') continue;
    val=piece_value(pc);
    if(val<=0) continue;
    if(!attacked_by(after,i,enemy)) continue;

    attacker=lowest_attacker_value(after,i,enemy);
    defended=attacked_by(after,i,perspective);

    if(!defended) penalty+=(double)val/95.0;
    else if(attacker>0 && attacker<val) penalty+=(double)(val-attacker)/120.0 + (double)val/650.0;
    else penalty+=(double)val/900.0;

    if(lp=='q') penalty+=2.0;
    else if(lp=='r') penalty+=0.45;
    else if(lp=='b' || lp=='n') penalty+=0.25;
  }
  return penalty;
}

static double tactical_reply_penalty(const Pos *after,int perspective){
  Move replies[MAX_MOVES];
  Pos q,r;
  int n,i,base,ev,drop,maxdrop;

  q=*after;
  gen_legal(&q,replies,&n);
  base=static_eval(after,perspective);
  maxdrop=0;
  for(i=0;i<n;i++){
    make_move(&q,&replies[i],&r);
    ev=static_eval(&r,perspective);
    drop=base-ev;
    if(drop>maxdrop) maxdrop=drop;
  }
  if(maxdrop<=0) return 0.0;
  return (double)maxdrop/140.0;
}

static int home_minor_count(const Pos *p,int side){
  int c;
  c=0;
  if(side==0){
    if(p->b[sq_of(1,0)]=='N') c++;
    if(p->b[sq_of(6,0)]=='N') c++;
    if(p->b[sq_of(2,0)]=='B') c++;
    if(p->b[sq_of(5,0)]=='B') c++;
  } else {
    if(p->b[sq_of(1,7)]=='n') c++;
    if(p->b[sq_of(6,7)]=='n') c++;
    if(p->b[sq_of(2,7)]=='b') c++;
    if(p->b[sq_of(5,7)]=='b') c++;
  }
  return c;
}

static double opening_penalty(const Pos *before,const Move *m,int perspective){
  char pc,cap,lp;
  int early,home_before,from_rank,to_rank;
  double p;

  pc=before->b[m->from];
  cap=before->b[m->to];
  lp=lower_piece(pc);
  early=before->fullmove<=12;
  p=0.0;
  if(!early) return 0.0;

  home_before=home_minor_count(before,perspective);
  from_rank=rank_of(m->from);
  to_rank=rank_of(m->to);

  if(lp=='q'){
    p+=1.15;
    if(cap=='.' || piece_value(cap)<=100) p+=0.55;
  }

  if((lp=='b' || lp=='n') && home_before>=2){
    if(perspective==0 && from_rank>1) p+=0.35;
    if(perspective==1 && from_rank<6) p+=0.35;
  }

  if(lp=='b' || lp=='n'){
    if(perspective==0 && to_rank>=5) p+=0.85;
    if(perspective==1 && to_rank<=2) p+=0.85;

    if(lp=='n'){
      if(perspective==0 && to_rank>=4) p+=0.75;
      if(perspective==1 && to_rank<=3) p+=0.75;
    }
  }

  if(lp=='r'){
    p+=1.20;
  }

  if(lp=='k' && !(m->flags & FLAG_CASTLE)) p+=1.0;

  
  {
    /* repeat_minor_guard:
       Early transformation cost for moving an already-developed minor
       piece again without capture and without direct check.

       It penalizes wasted transformation/tempo loops such as Bb5-d3-b5,
       while leaving first development, captures and checks untouched.
    */
    int home_from;
    int capture;
    int checks;
    Pos after_probe;

    home_from=0;
    if(lp=='b' || lp=='n'){
      if(perspective==0){
        if((m->from==sq_of(1,0) && pc=='N') ||
           (m->from==sq_of(6,0) && pc=='N') ||
           (m->from==sq_of(2,0) && pc=='B') ||
           (m->from==sq_of(5,0) && pc=='B')) home_from=1;
      } else {
        if((m->from==sq_of(1,7) && pc=='n') ||
           (m->from==sq_of(6,7) && pc=='n') ||
           (m->from==sq_of(2,7) && pc=='b') ||
           (m->from==sq_of(5,7) && pc=='b')) home_from=1;
      }

      capture=(cap!='.');
      checks=0;
      make_move(before,m,&after_probe);
      if(in_check(&after_probe,1-perspective)) checks=1;

      if(!home_from && !capture && !checks){
        p+=2.40;
      }
    }
  }

return p;
}

static double move_stability(const Pos *after,int perspective){
  int eval1,eval2;
  Pos q;
  q=*after;
  eval1=static_eval(after,perspective);
  q.side=1-perspective;
  eval2=static_eval(&q,perspective);
  return 1.0/(1.0+abs(eval1-eval2)/100.0);
}

static double state_complexity(const Pos *p){
  Move moves[MAX_MOVES];
  Pos q;
  int n;
  q=*p;
  gen_legal(&q,moves,&n);
  return (double)n/40.0;
}

static double state_forcing(const Pos *p){
  Move moves[MAX_MOVES];
  Pos q;
  int n;
  q=*p;
  gen_legal(&q,moves,&n);
  if(n<=0) return 2.0;
  if(in_check(p,p->side)) return 1.0 + (30.0-n)/30.0;
  return (30.0-n)/30.0;
}

static double state_tactic_pressure(const Pos *p,int perspective){
  Move moves[MAX_MOVES];
  Pos q,r;
  int n,i,base,ev,bestgain;
  q=*p;
  gen_legal(&q,moves,&n);
  base=static_eval(p,perspective);
  bestgain=0;
  for(i=0;i<n;i++){
    make_move(&q,&moves[i],&r);
    ev=static_eval(&r,perspective);
    if(ev-base>bestgain) bestgain=ev-base;
  }
  if(bestgain<=0) return 0.0;
  return (double)bestgain/140.0;
}

static double side_coherence(const Pos *p,int side){
  int home,developed,k,queen_home,rook_home;
  double c;

  home=home_minor_count(p,side);
  developed=4-home;
  c=0.0;

  c+=0.28*(double)developed;
  c-=0.10*(double)home;

  if(side==0){
    k=find_king(p,0);
    if(k==sq_of(6,0) || k==sq_of(2,0)) c+=0.75;
    if(k==sq_of(4,0) && p->fullmove>=8) c-=0.55;

    queen_home=(p->b[sq_of(3,0)]=='Q');
    rook_home=(p->b[sq_of(0,0)]=='R')+(p->b[sq_of(7,0)]=='R');

    if(!queen_home && p->fullmove<=10 && home>=2) c-=0.65;
    if(rook_home<2 && p->fullmove<=10 && k==sq_of(4,0)) c-=0.35;

    if(p->b[sq_of(3,3)]=='P') c+=0.18;
    if(p->b[sq_of(4,3)]=='P') c+=0.18;
  } else {
    k=find_king(p,1);
    if(k==sq_of(6,7) || k==sq_of(2,7)) c+=0.75;
    if(k==sq_of(4,7) && p->fullmove>=8) c-=0.55;

    queen_home=(p->b[sq_of(3,7)]=='q');
    rook_home=(p->b[sq_of(0,7)]=='r')+(p->b[sq_of(7,7)]=='r');

    if(!queen_home && p->fullmove<=10 && home>=2) c-=0.65;
    if(rook_home<2 && p->fullmove<=10 && k==sq_of(4,7)) c-=0.35;

    if(p->b[sq_of(3,4)]=='p') c+=0.18;
    if(p->b[sq_of(4,4)]=='p') c+=0.18;
  }

  return c;
}

static double state_coherence(const Pos *p,int perspective){
  double mine,opp;

  mine=side_coherence(p,perspective);
  opp=side_coherence(p,1-perspective);

  return mine-0.45*opp;
}

static double rough_position_score(const Pos *p,int perspective){
  double x;

  x=(double)static_eval(p,perspective)/100.0;
  x-=0.95*hanging_penalty(p,perspective);
  x-=0.30*state_complexity(p);
  x+=0.35*state_coherence(p,perspective);
  x+=0.30*state_activity(p,perspective);

  return x;
}

static double state_resilience(const Pos *p,int perspective){
  Move moves[MAX_MOVES];
  Pos q,r;
  int n,i;
  double base,best,worst,v;

  q=*p;
  gen_legal(&q,moves,&n);

  if(n<=0){
    if(in_check(p,p->side)){
      if(p->side==perspective) return -20.0;
      return 20.0;
    }
    return 0.0;
  }

  base=rough_position_score(p,perspective);

  if(p->side==perspective){
    best=-1e100;
    for(i=0;i<n;i++){
      make_move(&q,&moves[i],&r);
      v=rough_position_score(&r,perspective);
      if(v>best) best=v;
    }
    return best-base;
  }

  worst=1e100;
  for(i=0;i<n;i++){
    make_move(&q,&moves[i],&r);
    v=rough_position_score(&r,perspective);
    if(v<worst) worst=v;
  }

  return worst-base;
}

static double side_activity(const Pos *p,int side){
  int i,f,r,dist_file,dist_rank,mob;
  char pc,lp;
  double a;

  a=0.0;

  for(i=0;i<64;i++){
    pc=p->b[i];
    if(pc=='.' || piece_side(pc)!=side) continue;

    lp=lower_piece(pc);
    f=file_of(i);
    r=rank_of(i);

    if(lp=='n' || lp=='b'){
      /* Pezzi minori sviluppati verso il centro. */
      if(side==0){
        if(r>=2) a+=0.22;
        if(r>=3) a+=0.12;
      } else {
        if(r<=5) a+=0.22;
        if(r<=4) a+=0.12;
      }

      /* Pezzi ai bordi sono meno attivi, senza vietarli. */
      if(f==0 || f==7) a-=0.32;
      if((lp=='n') && (f==0 || f==7)) a-=0.28;

      /* Centro geometrico: bonus per vicinanza a d4/e4/d5/e5. */
      dist_file=abs(f-3);
      if(abs(f-4)<dist_file) dist_file=abs(f-4);
      dist_rank=abs(r-3);
      if(abs(r-4)<dist_rank) dist_rank=abs(r-4);

      a+=0.10*(double)(3-dist_file);
      a+=0.10*(double)(3-dist_rank);
    }

    if(lp=='q'){
      /* Donna attiva solo se non prematura: piccola cautela generale. */
      if(side==0 && r>=2 && p->fullmove>8) a+=0.10;
      if(side==1 && r<=5 && p->fullmove>8) a+=0.10;
    }

    if(lp=='r'){
      /* Torre su colonna centrale o avanzata è più attiva. */
      if(f==2 || f==3 || f==4 || f==5) a+=0.08;
      if(side==0 && r>=1) a+=0.05;
      if(side==1 && r<=6) a+=0.05;
    }

    if(lp=='p'){
      /* Spazio centrale: pedoni centrali avanzati in modo utile. */
      if(side==0){
        if((f==3 || f==4) && r>=3) a+=0.18;
        if((f==2 || f==5) && r>=3) a+=0.08;
      } else {
        if((f==3 || f==4) && r<=4) a+=0.18;
        if((f==2 || f==5) && r<=4) a+=0.08;
      }
    }
  }

  mob=mobility_for_side((Pos *)p,side);
  a+=0.025*(double)mob;

  return a;
}

static double state_activity(const Pos *p,int perspective){
  double mine,opp;

  mine=side_activity(p,perspective);
  opp=side_activity(p,1-perspective);

  return mine-0.45*opp;
}

static double burden_leaf_score(const Pos *p,int side){
  double x;

  x=(double)material_eval(p,side)/100.0;
  x+=0.04*(double)(mobility_for_side((Pos *)p,side)-mobility_for_side((Pos *)p,1-side));
  x+=0.22*state_activity(p,side);
  x+=0.18*state_coherence(p,side);
  x-=0.65*hanging_penalty(p,side);
  x-=0.40*move_risk(p,side);

  return x;
}

static double side_burden(const Pos *p,int side){
  Move moves[MAX_MOVES];
  Pos q,r;
  double vals[MAX_MOVES];
  int n,i,good;
  double base,v,best,avg,spread,good_ratio,b;

  q=*p;
  q.side=side;
  gen_legal(&q,moves,&n);

  if(n<=0){
    if(in_check(&q,side)) return 20.0;
    return 0.0;
  }

  base=burden_leaf_score(&q,side);
  best=-1e100;
  avg=0.0;

  for(i=0;i<n;i++){
    make_move(&q,&moves[i],&r);
    v=burden_leaf_score(&r,side);
    vals[i]=v;
    avg+=v;
    if(v>best) best=v;
  }

  avg/=(double)n;
  good=0;
  for(i=0;i<n;i++){
    if(vals[i]>=best-0.75) good++;
  }

  good_ratio=(double)good/(double)n;
  spread=best-avg;

  b=0.0;
  b+=0.85*(1.0-good_ratio);
  b+=0.32*spread;
  b+=0.40*hanging_penalty(&q,side);
  b+=0.25*move_risk(&q,side);
  if(base<0.0) b+=0.08*(-base);

  return b;
}

static double state_transfer(const Pos *p,int perspective){
  double mine,opp;

  mine=side_burden(p,perspective);
  opp=side_burden(p,1-perspective);

  return opp-mine;
}


/*
  Future option value.

  Non guarda la storia.
  Legge solo le trasformazioni future ancora disponibili nello stato FEN.

  Importante: un diritto FEN viene valorizzato solo se e' anche
  materialmente/legalmente possibile nello stato corrente. Quindi evita
  l'impossibile: per esempio K nella FEN senza re in e1 o torre in h1
  non produce valore.
*/

static int castle_option_possible_now(const Pos *p,int side,int kingside){
  int e,g,c,f,d,b,a,h;
  int enemy;
  char king,rook;

  enemy=1-side;

  if(side==0){
    king='K';
    rook='R';
    e=sq_of(4,0);
    g=sq_of(6,0);
    c=sq_of(2,0);
    f=sq_of(5,0);
    d=sq_of(3,0);
    b=sq_of(1,0);
    a=sq_of(0,0);
    h=sq_of(7,0);
  } else {
    king='k';
    rook='r';
    e=sq_of(4,7);
    g=sq_of(6,7);
    c=sq_of(2,7);
    f=sq_of(5,7);
    d=sq_of(3,7);
    b=sq_of(1,7);
    a=sq_of(0,7);
    h=sq_of(7,7);
  }

  if(p->b[e]!=king) return 0;
  if(attacked_by(p,e,enemy)) return 0;

  if(kingside){
    if(p->b[h]!=rook) return 0;
    if(p->b[f]!='.' || p->b[g]!='.') return 0;
    if(attacked_by(p,f,enemy)) return 0;
    if(attacked_by(p,g,enemy)) return 0;
    return 1;
  } else {
    if(p->b[a]!=rook) return 0;
    if(p->b[d]!='.' || p->b[c]!='.' || p->b[b]!='.') return 0;
    if(attacked_by(p,d,enemy)) return 0;
    if(attacked_by(p,c,enemy)) return 0;
    return 1;
  }
}

static int side_has_castled_shape_future(const Pos *p,int side){
  if(side==0){
    if(p->b[sq_of(6,0)]=='K') return 1;
    if(p->b[sq_of(2,0)]=='K') return 1;
  } else {
    if(p->b[sq_of(6,7)]=='k') return 1;
    if(p->b[sq_of(2,7)]=='k') return 1;
  }
  return 0;
}

static double castling_future_side(const Pos *p,int side){
  int wk,wq,bk,bq;
  int ksq;
  double v;

  wk=(p->castle & 1)?1:0;
  wq=(p->castle & 2)?1:0;
  bk=(p->castle & 4)?1:0;
  bq=(p->castle & 8)?1:0;

  v=0.0;

  if(side==0){
    if(wk && castle_option_possible_now(p,side,1)) v+=0.45;
    if(wq && castle_option_possible_now(p,side,0)) v+=0.35;
  } else {
    if(bk && castle_option_possible_now(p,side,1)) v+=0.45;
    if(bq && castle_option_possible_now(p,side,0)) v+=0.35;
  }

  /*
    Se la forma arroccata e' gia' nello stato, consideriamo la
    trasformazione incassata senza bisogno di memoria storica.
  */
  if(side_has_castled_shape_future(p,side)) v+=0.25;

  /*
    Perdita dell'opzione: se siamo ancora col re in casa, non arroccati,
    e non c'e' piu' nessun diritto possibile, la regione ha meno futuro.
    Peso piccolo e limitato alla fase iniziale.
  */
  ksq=find_king(p,side);

  if(side==0){
    if(!wk && !wq && ksq==sq_of(4,0) && p->fullmove<=14) v-=0.30;
    if(!side_has_castled_shape_future(p,side) &&
       ksq>=0 && ksq!=sq_of(4,0) && p->fullmove<=12) v-=0.25;
  } else {
    if(!bk && !bq && ksq==sq_of(4,7) && p->fullmove<=14) v-=0.30;
    if(!side_has_castled_shape_future(p,side) &&
       ksq>=0 && ksq!=sq_of(4,7) && p->fullmove<=12) v-=0.25;
  }

  return v;
}

static double ep_future_side(const Pos *p,int side){
  int f,r,from1,from2;
  char pawn;

  if(p->ep<0) return 0.0;
  if(p->side!=side) return 0.0;

  f=file_of(p->ep);
  r=rank_of(p->ep);
  pawn=(side==0)?'P':'p';

  if(side==0){
    from1=(f>0)?sq_of(f-1,r-1):-1;
    from2=(f<7)?sq_of(f+1,r-1):-1;
  } else {
    from1=(f>0)?sq_of(f-1,r+1):-1;
    from2=(f<7)?sq_of(f+1,r+1):-1;
  }

  if(from1>=0 && from1<64 && p->b[from1]==pawn) return 0.12;
  if(from2>=0 && from2<64 && p->b[from2]==pawn) return 0.12;

  return 0.0;
}

static double pawn_double_step_options_side(const Pos *p,int side){
  int f,rank,one,two;
  char pawn;
  double v;

  rank=(side==0)?1:6;
  pawn=(side==0)?'P':'p';
  v=0.0;

  for(f=0;f<8;f++){
    if(p->b[sq_of(f,rank)]!=pawn) continue;

    if(side==0){
      one=sq_of(f,2);
      two=sq_of(f,3);
    } else {
      one=sq_of(f,5);
      two=sq_of(f,4);
    }

    if(p->b[one]=='.' && p->b[two]=='.'){
      if(f>=2 && f<=5) v+=0.04;
      else v+=0.02;
    }
  }

  return v;
}

static double promotion_future_side(const Pos *p,int side){
  int i,r;
  char pc;
  double v;

  v=0.0;

  for(i=0;i<64;i++){
    pc=p->b[i];
    if(pc=='.') continue;
    if(piece_side(pc)!=side) continue;
    if(lower_piece(pc)!='p') continue;

    r=rank_of(i);

    if(side==0){
      if(r==5) v+=0.14;
      else if(r==6) v+=0.38;
    } else {
      if(r==2) v+=0.14;
      else if(r==1) v+=0.38;
    }
  }

  return v;
}

static double state_future_options(const Pos *p,int perspective){
  int enemy;
  double mine,opp,v;

  enemy=1-perspective;

  mine=0.0;
  opp=0.0;

  mine+=castling_future_side(p,perspective);
  mine+=ep_future_side(p,perspective);
  mine+=pawn_double_step_options_side(p,perspective);
  mine+=promotion_future_side(p,perspective);

  opp+=castling_future_side(p,enemy);
  opp+=ep_future_side(p,enemy);
  opp+=pawn_double_step_options_side(p,enemy);
  opp+=promotion_future_side(p,enemy);

  v=mine-0.65*opp;

  if(v>2.0) v=2.0;
  if(v<-2.0) v=-2.0;

  return v;
}


/*
  Stabilization relief.

  Misura diagnostica, non usata dalla funzione di scelta.
  Indica se lo stato ha una struttura che riduce il burden futuro
  rispetto a un centro fluido e non ancora sostenuto.
*/

static int sr_pawn_at(const Pos *p,int f,int r,int side){
  char pc;
  if(f<0 || f>7 || r<0 || r>7) return 0;
  pc=p->b[sq_of(f,r)];
  if(pc=='.') return 0;
  if(piece_side(pc)!=side) return 0;
  if(lower_piece(pc)!='p') return 0;
  return 1;
}

static int sr_king_home(const Pos *p,int side){
  if(side==0) return p->b[sq_of(4,0)]=='K';
  return p->b[sq_of(4,7)]=='k';
}

static int sr_minor_developed(const Pos *p,int side){
  int i,c;
  char pc,lp;

  c=0;

  for(i=0;i<64;i++){
    pc=p->b[i];
    if(pc=='.') continue;
    if(piece_side(pc)!=side) continue;

    lp=lower_piece(pc);
    if(lp!='n' && lp!='b') continue;

    if(side==0){
      if(i!=sq_of(1,0) && i!=sq_of(6,0) &&
         i!=sq_of(2,0) && i!=sq_of(5,0)) c++;
    } else {
      if(i!=sq_of(1,7) && i!=sq_of(6,7) &&
         i!=sq_of(2,7) && i!=sq_of(5,7)) c++;
    }
  }

  return c;
}

static int sr_enemy_mobile_center(const Pos *p,int side){
  int e;
  e=1-side;

  if(e==0){
    if(sr_pawn_at(p,3,3,e)) return 1;
    if(sr_pawn_at(p,4,3,e)) return 1;
    if(sr_pawn_at(p,3,1,e) && p->b[sq_of(3,2)]=='.') return 1;
    if(sr_pawn_at(p,4,1,e) && p->b[sq_of(4,2)]=='.') return 1;
    if(sr_pawn_at(p,2,1,e) && p->b[sq_of(2,2)]=='.') return 1;
  } else {
    if(sr_pawn_at(p,3,4,e)) return 1;
    if(sr_pawn_at(p,4,4,e)) return 1;
    if(sr_pawn_at(p,3,6,e) && p->b[sq_of(3,5)]=='.') return 1;
    if(sr_pawn_at(p,4,6,e) && p->b[sq_of(4,5)]=='.') return 1;
    if(sr_pawn_at(p,2,6,e) && p->b[sq_of(2,5)]=='.') return 1;
  }

  return 0;
}

static double sr_backbone_side(const Pos *p,int side){
  double v;

  v=0.0;

  if(side==0){
    if(sr_pawn_at(p,4,2,side)) v+=0.55; /* e3 */
    if(sr_pawn_at(p,2,2,side)) v+=0.38; /* c3 */
    if(sr_pawn_at(p,3,2,side)) v+=0.30; /* d3 */
    if(sr_pawn_at(p,4,3,side)) v+=0.45; /* e4 */
    if(sr_pawn_at(p,3,3,side)) v+=0.35; /* d4 */
  } else {
    if(sr_pawn_at(p,4,5,side)) v+=0.55; /* e6 */
    if(sr_pawn_at(p,2,5,side)) v+=0.38; /* c6 */
    if(sr_pawn_at(p,3,5,side)) v+=0.30; /* d6 */
    if(sr_pawn_at(p,4,4,side)) v+=0.45; /* e5 */
    if(sr_pawn_at(p,3,4,side)) v+=0.35; /* d5 */
  }

  return v;
}

static double side_stabilization_relief(const Pos *p,int side){
  double v,bb;
  int dev;
  int king_home;
  int enemy_mobile;

  bb=sr_backbone_side(p,side);
  dev=sr_minor_developed(p,side);
  king_home=sr_king_home(p,side);
  enemy_mobile=sr_enemy_mobile_center(p,side);

  v=0.0;
  v+=bb;

  if(enemy_mobile && dev>=2) v+=0.45*bb;

  if(enemy_mobile && king_home && bb<0.20) v-=0.45;
  if(enemy_mobile && dev>=2 && bb<0.20) v-=0.35;

  if(v>2.0) v=2.0;
  if(v<-2.0) v=-2.0;

  return v;
}

static double state_stabilization_relief(const Pos *p,int perspective){
  int enemy;
  double mine,opp,v;

  enemy=1-perspective;

  mine=side_stabilization_relief(p,perspective);
  opp=side_stabilization_relief(p,enemy);

  v=mine-0.65*opp;

  if(v>2.0) v=2.0;
  if(v<-2.0) v=-2.0;

  return v;
}

static Phi eval_phi_state(const Pos *p,int perspective){
  Phi z;
  z.value=(double)static_eval(p,perspective)/100.0;
  z.complexity=state_complexity(p);
  z.risk=move_risk(p,perspective);
  z.forcing=state_forcing(p);
  z.stability=move_stability(p,perspective);
  z.hanging=hanging_penalty(p,perspective);
  z.tactic=state_tactic_pressure(p,perspective);
  z.coherence=state_coherence(p,perspective);
  z.resilience=state_resilience(p,perspective);
  z.activity=state_activity(p,perspective);
  z.future=state_future_options(p,perspective);
  return z;
}

static Metrics eval_move(const Pos *p,const Move *m,int perspective){
  Pos after;
  Metrics x;
  int ev;
  make_move(p,m,&after);
  ev=static_eval(&after,perspective);
  x.value=(double)ev/100.0;
  x.complexity=move_complexity(&after);
  x.risk=move_risk(&after,perspective);
  x.forcing=move_forcing(&after,perspective);
  x.stability=move_stability(&after,perspective);
  x.hanging=hanging_penalty(&after,perspective);
  x.tactic=tactical_reply_penalty(&after,perspective);
  x.opening=opening_penalty(p,m,perspective);
  x.score=x.value - 0.65*x.complexity - 0.80*x.risk + 0.40*signed_forcing(x.value,x.forcing) + 0.25*x.stability - 1.20*x.hanging - 0.95*x.tactic - 0.45*x.opening + 0.45*state_coherence(&after,perspective) + 0.55*state_resilience(&after,perspective) + 0.50*state_activity(&after,perspective);
  return x;
}

static void move_to_uci(const Move *m,char out[8]){
  char a[3],b[3];
  square_name(m->from,a);
  square_name(m->to,b);
  out[0]=a[0]; out[1]=a[1]; out[2]=b[0]; out[3]=b[1];
  if(m->flags & FLAG_PROMO){ out[4]=(char)tolower((unsigned char)m->promo); out[5]=0; }
  else out[4]=0;
}

static double terminal_score(const Pos *p,int root_side){
  if(in_check(p,p->side)){
    if(p->side==root_side) return -10000.0;
    return 10000.0;
  }
  return 0.0;
}

static double signed_forcing(double value,double forcing){
  double sign;

  sign=tanh(value/4.0);

  return forcing*sign;
}

static double transformed_leaf_score(const Pos *p,int root_side){
  Phi z;
  double forcing_good;
  double score;

  z=eval_phi_state(p,root_side);

  forcing_good=signed_forcing(z.value,z.forcing);

  if(p->side==root_side) forcing_good=-forcing_good;

  score=0.0;
  score+=z.value;
  score-=0.45*z.complexity;
  score-=0.85*z.risk;
  score+=0.55*forcing_good;
  score+=0.20*z.stability;
  score-=1.10*z.hanging;
  score+=0.20*z.tactic;
  score+=0.55*z.coherence;
  score+=0.70*z.resilience;
  score+=0.55*z.activity;

  return score;
}

static int move_order_value(const Pos *p,const Move *m){
  char pc,cap;
  int v;

  pc=p->b[m->from];
  cap=p->b[m->to];
  v=0;

  if(m->flags & FLAG_CAPTURE){
    v+=10000;
    v+=10*piece_value(cap);
    v-=piece_value(pc);
  }

  if(m->flags & FLAG_PROMO) v+=9000;
  if(m->flags & FLAG_CASTLE) v+=500;
  if(lower_piece(pc)=='q') v-=200;
  if(lower_piece(pc)=='k' && !(m->flags & FLAG_CASTLE)) v-=300;

  return v;
}

static void order_moves(const Pos *p,Move *moves,int n){
  int i,j,best,bv,v;
  Move tmp;

  for(i=0;i<n;i++){
    best=i;
    bv=move_order_value(p,&moves[i]);
    for(j=i+1;j<n;j++){
      v=move_order_value(p,&moves[j]);
      if(v>bv){
        bv=v;
        best=j;
      }
    }
    if(best!=i){
      tmp=moves[i];
      moves[i]=moves[best];
      moves[best]=tmp;
    }
  }
}

static double search_score(const Pos *p,int depth,double alpha,double beta,int root_side){
  Move moves[MAX_MOVES];
  Pos child;
  int n,i;
  double best,v;

  gen_legal(p,moves,&n);

  if(n<=0) return terminal_score(p,root_side);
  if(depth<=0) return transformed_leaf_score(p,root_side);

  order_moves(p,moves,n);

  if(p->side==root_side){
    best=-1e100;
    for(i=0;i<n;i++){
      make_move(p,&moves[i],&child);
      v=search_score(&child,depth-1,alpha,beta,root_side);
      if(v>best) best=v;
      if(best>alpha) alpha=best;
      if(alpha>=beta) break;
    }
    return best;
  } else {
    best=1e100;
    for(i=0;i<n;i++){
      make_move(p,&moves[i],&child);
      v=search_score(&child,depth-1,alpha,beta,root_side);
      if(v<best) best=v;
      if(best<beta) beta=best;
      if(alpha>=beta) break;
    }
    return best;
  }
}

typedef struct {
  const Pos *p;
  Move *moves;
  int n;
  int tid;
  int threads;
  int perspective;
  Move best;
  Metrics bestm;
  double best_score;
  int found;
} RootWorker;

static int root_thread_count(void){
  const char *e;
  int n;

  n=ROOT_THREADS;
  e=getenv("SQCHESS_THREADS");
  if(e && *e){
    n=atoi(e);
  }

  if(n<1) n=1;
  if(n>ROOT_THREADS_MAX) n=ROOT_THREADS_MAX;

  return n;
}

static void *root_worker_main(void *arg){
  RootWorker *w;
  Pos after;
  Metrics m;
  double search,combined;
  int i;

  w=(RootWorker *)arg;
  w->found=0;
  w->best_score=-1e100;

  for(i=w->tid;i<w->n;i+=w->threads){
    make_move(w->p,&w->moves[i],&after);
    m=eval_move(w->p,&w->moves[i],w->perspective);
    search=search_score(&after,SEARCH_DEPTH-1,-1e100,1e100,w->perspective);
    /*
      transfer e' volutamente root-only:
      misura se la trasformazione candidata trasferisce burden all'avversario.
      Non viene propagato nelle foglie, per evitare rumore e costo esplosivo.
    */
    combined=0.55*m.score + 0.45*search + 0.55*state_transfer(&after,w->perspective);

    /*
      Decision v3:
      keep the stable decision unchanged, but add a small guard against
      transformed states where our stabilization relief is much worse
      than the opponent's.

      This is deliberately one-sided:
      - no reward for positive relief_balance;
      - no change when relief_balance is neutral;
      - only a penalty for clearly bad asymmetric states.
    */
    {
      double relief_me;
      double relief_opp;
      double relief_balance;
      double relief_guard;

      relief_me=state_stabilization_relief(&after,w->perspective);
      relief_opp=state_stabilization_relief(&after,1-w->perspective);
      relief_balance=relief_me-relief_opp;

      relief_guard=0.0;
      if(relief_balance < -1.50){
        relief_guard=0.22*(-1.50-relief_balance);
        combined-=relief_guard;
      }

      /*
        Minor sortie instability guard:
        in the early phase, a quiet minor-piece sortie is suspicious
        if it creates a high hanging exposure without direct forcing.

        This targets false transformations such as an active-looking
        bishop sortie that later becomes a tempo sink.
      */
      {
        char pc_sortie;
        char lp_sortie;
        int quiet_sortie;
        int minor_sortie;
        int gives_check_sortie;
        Pos sortie_after;
        double sortie_guard;
        int to_rank_sortie;
        int advanced_sortie;

        pc_sortie=w->p->b[w->moves[i].from];
        lp_sortie=lower_piece(pc_sortie);

        minor_sortie=(lp_sortie=='b' || lp_sortie=='n');
        quiet_sortie=(w->p->b[w->moves[i].to]=='.');

        gives_check_sortie=0;
        make_move(w->p,&w->moves[i],&sortie_after);
        if(in_check(&sortie_after,1-w->perspective)) gives_check_sortie=1;

        sortie_guard=0.0;
        to_rank_sortie=w->moves[i].to/8;
        advanced_sortie=0;

        if(w->perspective==0 && to_rank_sortie>=4) advanced_sortie=1;
        if(w->perspective==1 && to_rank_sortie<=3) advanced_sortie=1;

        if(w->p->fullmove<=30 && minor_sortie && quiet_sortie && !gives_check_sortie){
          if(advanced_sortie && m.hanging>0.75 && m.forcing<0.50){
            if(w->p->fullmove<=12) sortie_guard=1.55*(m.hanging-0.75); else sortie_guard=0.0;

            /*
              Extra decision-level cost if the sortie is not first development.
              This targets repeated advanced minor moves such as Bd3-b5.
            */
            {
              int home_from_sortie;
              home_from_sortie=0;

              if(w->perspective==0){
                if((w->moves[i].from==sq_of(1,0) && pc_sortie=='N') ||
                   (w->moves[i].from==sq_of(6,0) && pc_sortie=='N') ||
                   (w->moves[i].from==sq_of(2,0) && pc_sortie=='B') ||
                   (w->moves[i].from==sq_of(5,0) && pc_sortie=='B')) home_from_sortie=1;
              } else {
                if((w->moves[i].from==sq_of(1,7) && pc_sortie=='n') ||
                   (w->moves[i].from==sq_of(6,7) && pc_sortie=='n') ||
                   (w->moves[i].from==sq_of(2,7) && pc_sortie=='b') ||
                   (w->moves[i].from==sq_of(5,7) && pc_sortie=='b')) home_from_sortie=1;
              }

              if(!home_from_sortie){
                if(w->p->fullmove<=12) sortie_guard+=0.85;

                /*
                  Midgame repeated minor sortie guard:
                  if an already-developed minor piece makes a quiet advanced
                  sortie in a tactically hot state, treat it as a likely false
                  transformation. This targets moves such as Bd2-g5 when the
                  center is already unstable and tactical pressure is high.
                */
                if(w->p->fullmove>12 && w->p->fullmove<=30 && m.tactic>2.20 && m.hanging>1.00){
                  sortie_guard+=0.55*(m.tactic-2.20) + 0.25*(m.hanging-1.00);
                }
              }
            }

            combined-=sortie_guard;
          }
        }

        if(getenv("SQCHESS_DIAG")!=NULL && sortie_guard>0.0){
          char sortie_uci[8];
          move_to_uci(&w->moves[i],sortie_uci);
          fprintf(stderr,
            "DIAG_SORTIE_GUARD move=%s hanging=%.3f forcing=%.3f guard=%.3f\n",
            sortie_uci,m.hanging,m.forcing,sortie_guard);
        }
      }

      
      {
        /*
          Toxic capture guard:
          a minor piece capturing a pawn is not automatically progress.
          If the resulting state has high hanging exposure and high tactical
          pressure, the capture is treated as a destructive transformation.

          This targets cases such as Bd3xe4 where the move wins a pawn
          locally but produces a tactically broken state.
        */
        char tox_pc;
        char tox_cap;
        char tox_lp;
        char tox_cap_lp;
        int tox_checks;
        Pos tox_after;
        double toxic_guard;
        double toxic_pressure;

        tox_pc=w->p->b[w->moves[i].from];
        tox_cap=w->p->b[w->moves[i].to];
        tox_lp=lower_piece(tox_pc);
        tox_cap_lp=lower_piece(tox_cap);

        toxic_guard=0.0;

        tox_checks=0;
        if(tox_cap!='.'){
          make_move(w->p,&w->moves[i],&tox_after);
          if(in_check(&tox_after,1-w->perspective)) tox_checks=1;
        }

        /*
          General toxic capture:
          a capture is not automatically progress. If it is not check,
          not strongly forcing, and the resulting state has high hanging
          exposure plus high tactical pressure, treat it as destructive.

          The previous specific minor-captures-pawn case is kept inside this
          more general mechanism with a slightly lower threshold.
        */
        toxic_pressure=0.0;

        if(w->p->fullmove<=30 &&
           tox_cap!='.' &&
           !tox_checks &&
           m.forcing<0.90){

          if(m.hanging>3.00 && m.tactic>2.30){
            toxic_pressure=(m.hanging-3.00) + 0.55*(m.tactic-2.30);
          }

          if((tox_lp=='b' || tox_lp=='n') &&
             tox_cap_lp=='p' &&
             m.hanging>2.50 &&
             m.tactic>2.00){
            toxic_pressure+=(m.hanging-2.50) + 0.45*(m.tactic-2.00);
          }

          if(toxic_pressure>0.0){
            toxic_guard=1.05*toxic_pressure;
            combined-=toxic_guard;
          }
        }

        if(getenv("SQCHESS_DIAG")!=NULL && toxic_guard>0.0){
          char tox_uci[8];
          move_to_uci(&w->moves[i],tox_uci);
          fprintf(stderr,
            "DIAG_TOXIC_CAPTURE move=%s hanging=%.3f tactic=%.3f guard=%.3f\n",
            tox_uci,m.hanging,m.tactic,toxic_guard);
        }
      }


      {
        /*
          Pawn fork threat guard:
          after our candidate move, check whether the opponent has a quiet
          legal pawn push that would attack two of our minor pieces.

          This is a trajectory/state guard. It targets unresolved central
          pawn forks such as ...e5-e4 attacking Bd3 and Nf3 after castling.
        */
        Pos fork_q;
        Move fork_moves[MAX_MOVES];
        int fork_n;
        int fork_j;
        int opp_side;
        int to_file;
        int to_rank;
        int atk_rank;
        int atk_file;
        int attacked_minors;
        int k;
        int atk_sq;
        char pawn_pc;
        char victim;
        double fork_guard;
        double fork_max;

        fork_guard=0.0;
        fork_max=0.0;
        opp_side=1-w->perspective;

        fork_q=after;
        fork_q.side=opp_side;
        gen_legal(&fork_q,fork_moves,&fork_n);

        for(fork_j=0;fork_j<fork_n;fork_j++){
          pawn_pc=after.b[fork_moves[fork_j].from];

          if(lower_piece(pawn_pc)!='p') continue;

          /*
            Quiet pawn push only: same file, empty destination.
            Captures are handled by tactical/capture guards elsewhere.
          */
          if((fork_moves[fork_j].from%8)!=(fork_moves[fork_j].to%8)) continue;
          if(after.b[fork_moves[fork_j].to]!='.') continue;

          to_file=fork_moves[fork_j].to%8;
          to_rank=fork_moves[fork_j].to/8;

          if(opp_side==0) atk_rank=to_rank+1;
          else atk_rank=to_rank-1;

          if(atk_rank<0 || atk_rank>7) continue;

          attacked_minors=0;

          for(k=-1;k<=1;k+=2){
            atk_file=to_file+k;
            if(atk_file<0 || atk_file>7) continue;

            atk_sq=sq_of(atk_file,atk_rank);
            victim=after.b[atk_sq];

            if(w->perspective==0){
              if(victim=='N' || victim=='B') attacked_minors++;
            } else {
              if(victim=='n' || victim=='b') attacked_minors++;
            }
          }

          if(attacked_minors>=2){
            fork_guard=1.75 + 0.35*(attacked_minors-2);
            if(m.hanging>1.0) fork_guard+=0.25*(m.hanging-1.0);
            if(fork_guard>fork_max) fork_max=fork_guard;
          }
        }

        if(w->p->fullmove<=20 && fork_max>0.0){
          combined-=fork_max;
        }

        if(getenv("SQCHESS_DIAG")!=NULL && fork_max>0.0){
          char fork_uci[8];
          move_to_uci(&w->moves[i],fork_uci);
          fprintf(stderr,
            "DIAG_PAWN_FORK_THREAT move=%s hanging=%.3f guard=%.3f\n",
            fork_uci,m.hanging,fork_max);
        }
      }



      {
        /*
          Shield drift guard:
          a quiet second pawn push on the same wing as our king is a small
          transformation cost when it is non-forcing. This targets passive
          shield drift such as h3-h4 after castling, without touching the
          first luft move h2-h3 or forced/capturing pawn moves.
        */
        double shield_drift_guard;
        char sd_pc;
        int sd_from_file;
        int sd_to_file;
        int sd_from_rank;
        int sd_to_rank;
        int sd_king_sq;
        int sd_king_file;
        int sd_quiet;
        int sd_repeated_push;
        int sd_same_king_wing;

        shield_drift_guard=0.0;
        sd_pc=w->p->b[w->moves[i].from];
        sd_from_file=file_of(w->moves[i].from);
        sd_to_file=file_of(w->moves[i].to);
        sd_from_rank=rank_of(w->moves[i].from);
        sd_to_rank=rank_of(w->moves[i].to);
        sd_king_sq=find_king(w->p,w->perspective);
        sd_king_file=sd_king_sq>=0 ? file_of(sd_king_sq) : -1;

        sd_quiet=((w->moves[i].flags & FLAG_CAPTURE)==0 &&
                  (w->moves[i].flags & FLAG_EP)==0 &&
                  (w->moves[i].flags & FLAG_PROMO)==0);

        sd_repeated_push=0;
        if(w->perspective==0 && sd_from_rank>1 &&
           sd_to_rank==sd_from_rank+1 && sd_from_file==sd_to_file){
          sd_repeated_push=1;
        }
        if(w->perspective==1 && sd_from_rank<6 &&
           sd_to_rank==sd_from_rank-1 && sd_from_file==sd_to_file){
          sd_repeated_push=1;
        }

        sd_same_king_wing=0;
        if(sd_king_file>=5 && sd_from_file>=5) sd_same_king_wing=1;
        if(sd_king_file<=2 && sd_from_file<=2) sd_same_king_wing=1;

        if(w->p->fullmove<=35 &&
           lower_piece(sd_pc)=='p' &&
           sd_quiet &&
           sd_repeated_push &&
           sd_same_king_wing &&
           m.forcing<0.0){
          shield_drift_guard=0.16;
          shield_drift_guard+=0.18*(-m.forcing);
          if(m.risk>0.04) shield_drift_guard+=0.40*(m.risk-0.04);
          if(m.tactic>0.80) shield_drift_guard+=0.10*(m.tactic-0.80);
          if(shield_drift_guard>0.45) shield_drift_guard=0.45;
          combined-=shield_drift_guard;
        }

        if(getenv("SQCHESS_DIAG")!=NULL && shield_drift_guard>0.0){
          char sd_uci[8];
          move_to_uci(&w->moves[i],sd_uci);
          fprintf(stderr,
            "DIAG_SHIELD_DRIFT move=%s forcing=%.3f risk=%.3f tactic=%.3f guard=%.3f\n",
            sd_uci,m.forcing,m.risk,m.tactic,shield_drift_guard);
        }
      }


      {
        /*
          Forcing capture mirage guard:
          a capture can look forcing and materially attractive while the
          resulting state is overhanging and has negative transfer.
          This is deliberately small: it should only break close ties.
        */
        double fcm_guard;
        int fcm_is_capture;
        int fcm_gives_check;
        double fcm_transfer;

        fcm_guard=0.0;
        fcm_is_capture=((w->moves[i].flags & FLAG_CAPTURE)!=0 ||
                        (w->moves[i].flags & FLAG_EP)!=0);
        fcm_gives_check=in_check(&after,1-w->perspective);
        fcm_transfer=state_transfer(&after,w->perspective);

        if(w->p->fullmove<=30 &&
           fcm_is_capture &&
           m.forcing>1.00 &&
           m.hanging>4.00 &&
           m.tactic>2.00 &&
           fcm_transfer<-0.50){
          fcm_guard=0.10;
          fcm_guard+=0.08*(m.hanging-4.00);
          fcm_guard+=0.05*(m.tactic-2.00);
          if(m.forcing>1.50) fcm_guard+=0.08*(m.forcing-1.50);
          if(fcm_guard>0.55) fcm_guard=0.55;
          combined-=fcm_guard;
        }

        if(getenv("SQCHESS_DIAG")!=NULL && fcm_guard>0.0){
          char fcm_uci[8];
          move_to_uci(&w->moves[i],fcm_uci);
          fprintf(stderr,
            "DIAG_FORCING_CAPTURE_MIRAGE move=%s check=%d forcing=%.3f hanging=%.3f tactic=%.3f transfer=%.3f guard=%.3f\n",
            fcm_uci,fcm_gives_check,m.forcing,m.hanging,m.tactic,fcm_transfer,fcm_guard);
        }
      }



      {
        /*
          Shield vacancy intrusion guard:
          a two-square pawn push on the same wing as our castled king may
          vacate an entry square, typically h2 after h2-h4. If an enemy queen
          or bishop has an immediate legal move to that vacated square, the
          move receives a small transformation-state penalty.
        */
        double svi_guard;
        char svi_pc;
        int svi_from_file;
        int svi_to_file;
        int svi_from_rank;
        int svi_to_rank;
        int svi_king_sq;
        int svi_king_file;
        int svi_quiet;
        int svi_double_shield;
        int svi_same_king_wing;
        int svi_intrusion;
        Pos svi_opp;
        Move svi_moves[MAX_MOVES];
        int svi_n;
        int svi_j;

        svi_guard=0.0;
        svi_intrusion=0;

        svi_pc=w->p->b[w->moves[i].from];
        svi_from_file=file_of(w->moves[i].from);
        svi_to_file=file_of(w->moves[i].to);
        svi_from_rank=rank_of(w->moves[i].from);
        svi_to_rank=rank_of(w->moves[i].to);
        svi_king_sq=find_king(w->p,w->perspective);
        svi_king_file=svi_king_sq>=0 ? file_of(svi_king_sq) : -1;

        svi_quiet=((w->moves[i].flags & FLAG_CAPTURE)==0 &&
                   (w->moves[i].flags & FLAG_EP)==0 &&
                   (w->moves[i].flags & FLAG_PROMO)==0);

        svi_double_shield=0;
        if(w->perspective==0 &&
           svi_from_rank==1 &&
           svi_to_rank==3 &&
           svi_from_file==svi_to_file){
          svi_double_shield=1;
        }
        if(w->perspective==1 &&
           svi_from_rank==6 &&
           svi_to_rank==4 &&
           svi_from_file==svi_to_file){
          svi_double_shield=1;
        }

        svi_same_king_wing=0;
        if(svi_king_file>=5 && svi_from_file>=5) svi_same_king_wing=1;
        if(svi_king_file<=2 && svi_from_file<=2) svi_same_king_wing=1;

        if(w->p->fullmove<=30 &&
           lower_piece(svi_pc)=='p' &&
           svi_quiet &&
           svi_double_shield &&
           svi_same_king_wing &&
           m.forcing<0.20){
          svi_opp=after;
          svi_opp.side=1-w->perspective;
          gen_legal(&svi_opp,svi_moves,&svi_n);

          for(svi_j=0;svi_j<svi_n;svi_j++){
            char apc;
            apc=svi_opp.b[svi_moves[svi_j].from];
            if(svi_moves[svi_j].to==w->moves[i].from &&
               (lower_piece(apc)=='q' || lower_piece(apc)=='b')){
              svi_intrusion=1;
              break;
            }
          }

          if(svi_intrusion){
            svi_guard=0.06;
            if(m.forcing<0.0) svi_guard+=0.04*(-m.forcing);
            if(m.tactic>0.80) svi_guard+=0.03*(m.tactic-0.80);
            if(m.risk>0.04) svi_guard+=0.15*(m.risk-0.04);
            if(svi_guard>0.18) svi_guard=0.18;
            combined-=svi_guard;
          }
        }

        if(getenv("SQCHESS_DIAG")!=NULL && svi_guard>0.0){
          char svi_uci[8];
          move_to_uci(&w->moves[i],svi_uci);
          fprintf(stderr,
            "DIAG_SHIELD_VACANCY_INTRUSION move=%s forcing=%.3f risk=%.3f tactic=%.3f guard=%.3f\n",
            svi_uci,m.forcing,m.risk,m.tactic,svi_guard);
        }
      }

      {
        /*
          First shield hook guard:
          a first quiet pawn push on the same wing as our king has a small
          cost when the destination square can be immediately captured by an
          enemy bishop or queen. This targets h2-h3 when the c8-h3 diagonal
          is open, without penalizing the already-existing repeated shield
          drift rule.
        */
        double fsh_guard;
        char fsh_pc;
        int fsh_from_file;
        int fsh_to_file;
        int fsh_from_rank;
        int fsh_to_rank;
        int fsh_king_sq;
        int fsh_king_file;
        int fsh_quiet;
        int fsh_first_push;
        int fsh_same_king_wing;
        int fsh_hooked;
        Pos fsh_opp;
        Move fsh_moves[MAX_MOVES];
        int fsh_n;
        int fsh_j;

        fsh_guard=0.0;
        fsh_hooked=0;

        fsh_pc=w->p->b[w->moves[i].from];
        fsh_from_file=file_of(w->moves[i].from);
        fsh_to_file=file_of(w->moves[i].to);
        fsh_from_rank=rank_of(w->moves[i].from);
        fsh_to_rank=rank_of(w->moves[i].to);
        fsh_king_sq=find_king(w->p,w->perspective);
        fsh_king_file=fsh_king_sq>=0 ? file_of(fsh_king_sq) : -1;

        fsh_quiet=((w->moves[i].flags & FLAG_CAPTURE)==0 &&
                   (w->moves[i].flags & FLAG_EP)==0 &&
                   (w->moves[i].flags & FLAG_PROMO)==0);

        fsh_first_push=0;
        if(w->perspective==0 &&
           fsh_from_rank==1 &&
           fsh_to_rank==2 &&
           fsh_from_file==fsh_to_file){
          fsh_first_push=1;
        }
        if(w->perspective==1 &&
           fsh_from_rank==6 &&
           fsh_to_rank==5 &&
           fsh_from_file==fsh_to_file){
          fsh_first_push=1;
        }

        fsh_same_king_wing=0;
        if(fsh_king_file>=5 && fsh_from_file>=5) fsh_same_king_wing=1;
        if(fsh_king_file<=2 && fsh_from_file<=2) fsh_same_king_wing=1;

        if(w->p->fullmove<=30 &&
           lower_piece(fsh_pc)=='p' &&
           fsh_quiet &&
           fsh_first_push &&
           fsh_same_king_wing &&
           m.forcing<0.20){
          fsh_opp=after;
          fsh_opp.side=1-w->perspective;
          gen_legal(&fsh_opp,fsh_moves,&fsh_n);

          for(fsh_j=0;fsh_j<fsh_n;fsh_j++){
            char apc;
            apc=fsh_opp.b[fsh_moves[fsh_j].from];
            if(fsh_moves[fsh_j].to==w->moves[i].to &&
               ((fsh_moves[fsh_j].flags & FLAG_CAPTURE)!=0) &&
               (lower_piece(apc)=='b' || lower_piece(apc)=='q')){
              fsh_hooked=1;
              break;
            }
          }

          if(fsh_hooked){
            fsh_guard=0.06;
            if(m.forcing<0.0) fsh_guard+=0.06*(-m.forcing);
            if(m.tactic>0.80) fsh_guard+=0.04*(m.tactic-0.80);
            if(m.risk>0.04) fsh_guard+=0.20*(m.risk-0.04);
            if(fsh_guard>0.22) fsh_guard=0.22;
            combined-=fsh_guard;
          }
        }

        if(getenv("SQCHESS_DIAG")!=NULL && fsh_guard>0.0){
          char fsh_uci[8];
          move_to_uci(&w->moves[i],fsh_uci);
          fprintf(stderr,
            "DIAG_FIRST_SHIELD_HOOK move=%s forcing=%.3f risk=%.3f tactic=%.3f guard=%.3f\n",
            fsh_uci,m.forcing,m.risk,m.tactic,fsh_guard);
        }
      }

if(getenv("SQCHESS_DIAG")!=NULL){
        char diag_uci[8];
        move_to_uci(&w->moves[i],diag_uci);
        fprintf(stderr,
          "DIAG_DECISION_V3 move=%s search=%.3f imm=%.3f transfer=%.3f "
          "relief_balance=%.3f relief_guard=%.3f combined=%.3f\n",
          diag_uci,search,m.score,state_transfer(&after,w->perspective),
          relief_balance,relief_guard,combined);
      }
    }

    if(!w->found || combined>w->best_score){
      w->found=1;
      w->best_score=combined;
      w->best=w->moves[i];
      w->bestm=m;
      w->bestm.score=combined;
    }
  }

  return 0;
}

static int choose_move(const Pos *p,Move *best,Metrics *bestm){
  Move moves[MAX_MOVES];
  pthread_t tids[ROOT_THREADS_MAX];
  RootWorker workers[ROOT_THREADS_MAX];
  int n,i,threads,created,best_idx;
  double best_score;

  gen_legal((Pos *)p,moves,&n);
  if(n<=0){
    memset(best,0,sizeof(*best));
    memset(bestm,0,sizeof(*bestm));
    return 0;
  }

  order_moves(p,moves,n);

  threads=root_thread_count();
  if(threads>n) threads=n;

  created=0;
  for(i=0;i<threads;i++){
    workers[i].p=p;
    workers[i].moves=moves;
    workers[i].n=n;
    workers[i].tid=i;
    workers[i].threads=threads;
    workers[i].perspective=p->side;
    workers[i].found=0;
    workers[i].best_score=-1e100;

    if(pthread_create(&tids[i],0,root_worker_main,&workers[i])==0){
      created++;
    } else {
      break;
    }
  }

  if(created<threads){
    for(i=0;i<created;i++){
      pthread_join(tids[i],0);
    }

    workers[0].p=p;
    workers[0].moves=moves;
    workers[0].n=n;
    workers[0].tid=0;
    workers[0].threads=1;
    workers[0].perspective=p->side;
    workers[0].found=0;
    workers[0].best_score=-1e100;
    root_worker_main(&workers[0]);

    if(!workers[0].found){
      memset(best,0,sizeof(*best));
      memset(bestm,0,sizeof(*bestm));
      return 0;
    }

    *best=workers[0].best;
    *bestm=workers[0].bestm;
    return 1;
  }

  for(i=0;i<created;i++){
    pthread_join(tids[i],0);
  }

  best_idx=-1;
  best_score=-1e100;
  for(i=0;i<created;i++){
    if(workers[i].found && (best_idx<0 || workers[i].best_score>best_score)){
      best_idx=i;
      best_score=workers[i].best_score;
    }
  }

  if(best_idx<0){
    memset(best,0,sizeof(*best));
    memset(bestm,0,sizeof(*bestm));
    return 0;
  }

  *best=workers[best_idx].best;
  *bestm=workers[best_idx].bestm;
  return 1;
}



/*
  Standard FEN interface helper.

  External interface:
      ./sqchess "<full FEN>"
  or:
      ./sqchess <board> <side> <castling> <ep> <halfmove> <fullmove>

  This keeps all non-repeatable future options inside the current state:
      castling rights
      en-passant square
      halfmove clock
      fullmove number

  No history is needed. We only read the residual options encoded in FEN.
*/
static const char *fen_from_argv(int argc,char **argv,char *buf,size_t bufsz){
  int i;
  size_t used,need;

  if(argc<=1) return NULL;

  buf[0]='\0';
  used=0;

  for(i=1;i<argc;i++){
    need=strlen(argv[i]) + ((i>1)?1:0);
    if(used+need+1>=bufsz) return NULL;

    if(i>1){
      buf[used++]=' ';
      buf[used]='\0';
    }

    strcpy(buf+used,argv[i]);
    used+=strlen(argv[i]);
  }

  return buf;
}


int main(int argc,char **argv){
  const char *fen;
  char fenbuf[512];
  Pos p;
  Pos after;
  Move best;
  Metrics bm;
  char uci[8];

  fen=fen_from_argv(argc,argv,fenbuf,sizeof(fenbuf));

  if(fen==NULL){
    fprintf(stderr,"usage: %s \"<full FEN>\"\n",argv[0]);
    fprintf(stderr,"example: %s \"rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1\"\n",argv[0]);
    return 1;
  }

  if(!parse_fen(fen,&p)){
    fprintf(stderr,"invalid fen\n");
    return 1;
  }

  if(!choose_move(&p,&best,&bm)){
    if(in_check(&p,p.side)) printf("checkmate or illegal position\n");
    else printf("stalemate\n");
    return 0;
  }

  move_to_uci(&best,uci);
  make_move(&p,&best,&after);

  if(getenv("SQCHESS_EXPLAIN")!=NULL){
    int me;
    int opp;
    double me_burden,opp_burden;
    double me_transfer,opp_transfer;
    double me_relief,opp_relief;
    double me_future,opp_future;
    double me_activity,opp_activity;
    double me_coherence,opp_coherence;
    double me_resilience,opp_resilience;
    double me_hanging,opp_hanging;
    double me_tactic,opp_tactic;
    double me_risk,opp_risk;

    me=p.side;
    opp=1-me;

    me_burden=side_burden(&after,me);
    opp_burden=side_burden(&after,opp);

    me_transfer=state_transfer(&after,me);
    opp_transfer=state_transfer(&after,opp);

    me_relief=state_stabilization_relief(&after,me);
    opp_relief=state_stabilization_relief(&after,opp);

    me_future=state_future_options(&after,me);
    opp_future=state_future_options(&after,opp);

    me_activity=state_activity(&after,me);
    opp_activity=state_activity(&after,opp);

    me_coherence=state_coherence(&after,me);
    opp_coherence=state_coherence(&after,opp);

    me_resilience=state_resilience(&after,me);
    opp_resilience=state_resilience(&after,opp);

    me_hanging=hanging_penalty(&after,me);
    opp_hanging=hanging_penalty(&after,opp);

    me_tactic=state_tactic_pressure(&after,me);
    opp_tactic=state_tactic_pressure(&after,opp);

    me_risk=move_risk(&after,me);
    opp_risk=move_risk(&after,opp);

    fprintf(stderr,
      "EXPLAIN_BOTH move=%s score=%.3f "
      "me=value:%.3f activity:%.3f coherence:%.3f resilience:%.3f risk:%.3f hanging:%.3f tactic:%.3f burden:%.3f transfer:%.3f relief:%.3f future:%.3f "
      "opp=activity:%.3f coherence:%.3f resilience:%.3f risk:%.3f hanging:%.3f tactic:%.3f burden:%.3f transfer:%.3f relief:%.3f future:%.3f "
      "move_metrics=value:%.3f complexity:%.3f risk:%.3f forcing:%.3f stability:%.3f hanging:%.3f tactic:%.3f opening:%.3f\n",
      uci,bm.score,
      bm.value,me_activity,me_coherence,me_resilience,me_risk,me_hanging,me_tactic,me_burden,me_transfer,me_relief,me_future,
      opp_activity,opp_coherence,opp_resilience,opp_risk,opp_hanging,opp_tactic,opp_burden,opp_transfer,opp_relief,opp_future,
      bm.value,bm.complexity,bm.risk,bm.forcing,bm.stability,bm.hanging,bm.tactic,bm.opening);
  }

  printf("bestmove %s\n",uci);
  printf("score %.3f\n",bm.score);
  printf("search_depth %d\n",SEARCH_DEPTH);

  return 0;
}
