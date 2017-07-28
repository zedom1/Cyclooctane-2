#include "cyclooctane2.h"
using namespace std;
#pragma warning(disable:4244)
#pragma warning(disable:4305)
#pragma warning(disable:4996)

/////////// 常量 ////////////////
const double pi=3.1415926535;
const double pi2=2*pi;
const int MAX_INT=0x7FFFFFFF;
const int MIN_INT=-MAX_INT-1;
const double MAX_DOUBLE=1.79769e+308;
const double MIN_DOUBLE=-MAX_DOUBLE;
const double Obstacle::r=20.0;

/////////// 变量 ////////////////
int Bullet::num_time_count=0;
int Monster::num_count=0;
int Monster::num_total=0;
int Game::num_monster_fresh=0;
int Game::coin=0;
int Game::room_count=0;
int Bullet::range[]={0,20,0,400,500,15,0};
double Bullet::speed[]={0,15,0,0,0,15,22};
int shop_transport=2;

/////////// 全局对象 //////////////
Vector temp_vector;
Game cyclooctane,empt;
MENU_START s1;
MENU_SKILL s8;
MENU_CHA s2;  
ON_GAME s3;  
MENU_PAUSE s4;  
MENU_DEAD s5;  
EXIT s6;
SHOP1 s7;
SHOP2 s9;
HELP s10;
State* FSM::current=NULL; 
Node mapp[45][45];
IMAGE img_heart1 , img_heart2 , img_heart3 , img_empt , img_cha1 , img_cha2 , img_cha3;
IMAGE img_ski1,img_ski2,img_ski3,img_ski4,img_ski5,img_ski6,img_ski_null;
IMAGE img_coin1,img_coin2;
IMAGE img_help1,img_help2,img_help3,img_help4,img_help5,img_help6,img_help7,img_help8;

/////////// 全局函数 ////////////////
int normalize_x(double x)  //找到坐标所在方格的中心点x坐标
{
	double pos_x=900-495;  //pos_y=495-360;
	int ans1=((x-pos_x)/(2*Obstacle::r) );
	double ans=(ans1)*2*Obstacle::r+pos_x+Obstacle::r;
	return ans;
} 
int normalize_y(double y)   //找到坐标所在方格的中心点y坐标
{
	double pos_y=495-495;
	int ans1=((y-pos_y)/(2*Obstacle::r) );
	double ans=(ans1)*2*Obstacle::r+pos_y+Obstacle::r;
	return ans;
}
int get_i(double x)   //该中心对应mapp的i值
{
	double pos_x=900-495;
	return (x-pos_x-Obstacle::r)/(2*Obstacle::r);
}
int get_j(double y)  // 该中心对应mapp的j值
{
	double pos_y=495-495;
	return (y-pos_y-Obstacle::r)/(2*Obstacle::r);
}
int get_x_from_i(int i)
{
	double pos_x=900-495;
	return (i*(2*Obstacle::r))+pos_x+Obstacle::r;
}
int get_y_from_j(int j)
{
	double pos_y=495-495;
	return (j*(2*Obstacle::r))+pos_y+Obstacle::r;
}
void quicksort(int first, int last , Node* a)
{
	int i,j;
	Node tem,t;
	tem=a[first];
	i=first; j=last;
	if(i>j) return;
	while(i!=j)
	{
		while(i<j && a[j].cal_fx()>=tem.cal_fx())
			j--;
		while(i<j && a[i].cal_fx()<=tem.cal_fx())
			i++;
		if(i<j)
		{
			t=a[j]; a[j]=a[i]; a[i]=t;
		}
	}
	a[first]=a[j]; a[i]=tem;
	quicksort(first, i-1,a);
	quicksort(i+1,last,a);
	return;
}
bool judge_coll_line(POINT a , POINT b, POINT c, POINT d, POINT &cut)  // 检测线段相交
{
	double det=(b.x-a.x)*(c.y-d.y)-(c.x-d.x)*(b.y-a.y);
	if(abs(det)<1e-6) return false;
	double n1=((b.x-a.x)*(c.y-a.y)-(c.x-a.x)*(b.y-a.y) )/det;
	if(n1>1 || n1<0) return false;
	n1=((c.x-a.x)*(c.y-d.y)-(c.x-d.x)*(c.y-a.y) )/det;
	if(n1>1 || n1<0) return false;
	cut.x=a.x+n1*(b.x-a.x);
	cut.y=a.y+n1*(b.y-a.y);
	return true;
}
double point_to_line(POINT a, POINT head, POINT last)  // 点到线的距离
{
	Vector head_a(head,a),last_a(last,a),head_last(head,last);
	double r=head_a.dotmulti(head_last)/(head_last.get_lenth()*head_last.get_lenth());
	if(r<=0)
		return head_a.get_lenth();
	if(r>=1)
		return last_a.get_lenth();
	double xita=head_a.dotmulti(head_last)/(head_last.get_lenth()*head_a.get_lenth());
	return head_a.get_lenth()*sqrt(1-xita*xita);
}
bool judge_coll_single(POINT first[], int num_first, POINT second[], int num_second, Vector& shadow, double& num_move)  
	// 两凸多边形的碰撞检测  shadow为最小方向，num_move为最小分离距离
{
	double min_move=MAX_DOUBLE;
	int flag=0;
	for(int i=0; i<num_first; i++)   // 求第一个图形的各个投影轴
	{
		double maxn_first=MIN_DOUBLE,minx_first=MAX_DOUBLE;
		double maxn_second=MIN_DOUBLE,minx_second=MAX_DOUBLE;
		int j=i+1;
		Vector *v1=new Vector( first[i].x,first[i].y);
		Vector *v2=new Vector( first[j].x,first[j].y);
		Vector edge(*v1-*v2);  // 得到第一个图形的一条边向量
		edge.vertical();  // 求得边的垂直向量作为投影轴
		edge.new_normalize();   // 计算投影轴的单位向量

		for(int k=0; k<num_first; k++)    // 在该投影轴下第一个图图形的最大及最小投影值
		{
			Vector tem(first[k].x,first[k].y);
			double tot=tem.dotmulti(edge);
			maxn_first=max(tot,maxn_first);
			minx_first=min(tot,minx_first);		
		}
		for(int k=0; k<num_second; k++)
		{
			Vector tem(second[k].x,second[k].y);
			double tot=tem.dotmulti(edge);
			maxn_second=max(tot,maxn_second);
			minx_second=min(tot,minx_second);
		}
		if( (minx_second>maxn_first) || (minx_first>maxn_second)   )  // 代表中间有空隙
		{	flag=1; break; }
		if(minx_second<=maxn_first)
		{
			if(abs(min_move)>=abs(minx_second-maxn_first))
			{	
				shadow=edge;
				min_move=abs(minx_second-maxn_first);
			}
		}
		else if(minx_first<=maxn_second)
		{
			if(abs(min_move)>=abs(minx_first-maxn_second))
			{	
				shadow=edge;
				min_move=abs(minx_first-maxn_second);
			}
		}
	}
	if(flag==1)
		return false;  // false代表没有发生碰撞
	for(int i=0; i<num_second; i++)   // 求第二个图形的各个投影轴
	{
		double maxn_first=MIN_DOUBLE,minx_first=MAX_DOUBLE;
		double maxn_second=MIN_DOUBLE,minx_second=MAX_DOUBLE;
		int j=i+1;
		Vector *v1=new Vector( second[i].x,second[i].y);
		Vector *v2=new Vector( second[j].x,second[j].y);
		Vector edge(*v1-*v2);  // 得到第二个图形的一条边向量
		edge.vertical();  // 求得边的垂直向量作为投影轴
		edge.new_normalize();   // 计算投影轴的单位向量

		for(int k=0; k<num_first; k++)    // 在该投影轴下第一个图形的最大及最小投影值
		{
			Vector tem(first[k].x,first[k].y);
			double tot=tem.dotmulti(edge);
			maxn_first=max(tot,maxn_first);
			minx_first=min(tot,minx_first);
		}
		for(int k=0; k<num_second; k++)
		{
			Vector tem(second[k].x,second[k].y);
			double tot=tem.dotmulti(edge);
			maxn_second=max(tot,maxn_second);
			minx_second=min(tot,minx_second);
		}
		if( (minx_second>maxn_first) || (minx_first>maxn_second)   )  // 代表中间有空隙
		{	flag=1; break; }
		if(minx_second<=maxn_first)
		{
			if(abs(min_move)>=abs(minx_second-maxn_first))
			{	
				shadow=edge;
				min_move=abs(minx_second-maxn_first);
			}
		}
		else if(minx_first<=maxn_second)
		{
			if(abs(min_move)>=abs(minx_first-maxn_second))
			{	
				shadow=edge;
				min_move=abs(minx_first-maxn_second);
			}
		}
	}
	if(flag==1)
		return false;  // false代表没有发生碰撞
	num_move=min_move;
	return true;  //true代表发生了碰撞
}
bool judge_circle_coll(Vector circle_up, Vector circle_down,POINT second[],int num_second)
{
	// 圆和凸多边形的碰撞检测，未加入分离功能，用于检测子弹和怪物
	int flag=0;
	Vector edge;   
	double minx=MAX_DOUBLE;
	double mid_circle_x=(circle_up.x+circle_down.x)*1.0/2.0,mid_circle_y=(circle_up.y+circle_down.y)*1.0/2.0;
	for(int i=0; i<num_second ; i++) // 找出多边形与圆心距离最小的点，并将连线作为投影轴
	{
		double tot= (mid_circle_x-second[i].x)*(mid_circle_x-second[i].x)+(mid_circle_y-second[i].y)*(mid_circle_y-second[i].y) ;
		if(tot<minx)
		{
			edge.x=mid_circle_x-second[i].x;
			edge.y=mid_circle_y-second[i].y;
		}
	}
	edge.new_normalize();   // 计算投影轴的单位向量

	double maxn_first=MIN_DOUBLE,minx_first=MAX_DOUBLE;
	double maxn_second=MIN_DOUBLE,minx_second=MAX_DOUBLE;

	{  // 找出子弹在投影轴的投影值
		double tot=circle_up.dotmulti(edge);
		maxn_first=max(tot,maxn_first);
		minx_first=min(tot,minx_first);	
		tot=circle_down.dotmulti(edge);
		maxn_first=max(tot,maxn_first);
		minx_first=min(tot,minx_first);
	}
	for(int k=0; k<num_second; k++) //找出多边形在投影轴的投影值
	{
		Vector tem(second[k].x,second[k].y);
		double tot=tem.dotmulti(edge);
		maxn_second=max(tot,maxn_second);
		minx_second=min(tot,minx_second);
	}
	if( (minx_second>maxn_first) || (minx_first>maxn_second)   )  // 代表中间有空隙
		return false;  // false代表没有发生碰撞
	
	return true;  //true代表发生了碰撞
}
bool judge_p_left_right(POINT a, POINT line1, POINT line2)
//  判断点在向量的左右
{  // line1 -> line2
	double x=(line2.x-line1.x)*(a.y-line1.y)-(line2.y-line1.y)*(a.x-line1.x);
	return x<0; // x>0-> false -> left   // x<0->true -> right
}
void initi()
{
	srand((unsigned)time(NULL));
	initgraph(1200,800);
	setaspectratio(0.8,0.808081);
	setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 255 , 0 , 0 ));
	setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 0 , 0 , 0 ));
	settextstyle(80,40,_T("方正姚体"));  settextcolor(RGB(255,255,255));
	settextstyle(160,60,_T("微软雅黑"));  settextcolor(RGB(255,255,255));
	settextstyle(40,15,_T("微软雅黑"));  settextcolor(RGB(255,255,255));
	loadimage(&img_heart1,_T("BMP"),_T("heart1"),40,40);
	loadimage(&img_heart2,_T("BMP"),_T("heart2"),40,40);
	loadimage(&img_heart3,_T("BMP"),_T("heart3"),40,40);
	loadimage(&img_ski1,_T("BMP"),_T("bullet"),100,100);
	loadimage(&img_ski2,_T("BMP"),_T("rotate"),100,100);
	loadimage(&img_ski3,_T("BMP"),_T("laser1"),100,100);
	loadimage(&img_ski4,_T("BMP"),_T("laser2"),100,100);
	loadimage(&img_ski5,_T("BMP"),_T("boom"),100,100);
	loadimage(&img_ski6,_T("BMP"),_T("eater"),100,100);
	loadimage(&img_ski_null,_T("BMP"),_T("null"),100,100);
	loadimage(&img_coin1,_T("BMP"),_T("coin"),70,70);
	loadimage(&img_coin2,_T("BMP"),_T("soul"),70,70);
	loadimage(&img_help1,_T("jpg"),_T("help1"),1100,900);
	loadimage(&img_help2,_T("jpg"),_T("help2"),1100,900);
	loadimage(&img_help3,_T("jpg"),_T("help3"),1100,900);
	loadimage(&img_help4,_T("jpg"),_T("help4"),1100,900);
	loadimage(&img_help5,_T("jpg"),_T("help5"),1100,900);
	loadimage(&img_help6,_T("jpg"),_T("help6"),1100,900);
	loadimage(&img_help7,_T("jpg"),_T("help7"),1100,900);
	loadimage(&img_help8,_T("jpg"),_T("help8"),1100,900);
	getimage(&img_empt, 0  , 750,225 ,50);
	FSM::reset();
}

/////////// Node ////////////////
Node &Node::operator=( Node &a)
{
	(*this).fx=a.fx;
	(*this).gx=a.gx;
	(*this).hx=a.hx;
	(*this).pos.x=a.pos.x;
	(*this).pos.y=a.pos.y;
	(*this).fa.x=a.fa.x;
	(*this).fa.y=a.fa.y;
	(*this).ground=a.ground;
	return *this;
}
bool Node::operator == (Node a)
{
	return (this->fx==a.fx&&this->gx==a.gx&&this->hx==a.hx&&this->pos.x==a.pos.x&&this->pos.y==a.pos.y&&this->fa.x==a.fa.x&&this->fa.y==a.fa.y);
}
bool Node::operator != (Node a)
{
	return  !(*this==a);
}
Node::Node()
{
	fx=gx=hx=0;
	ground=0;
}
Node::~Node(){}
Node::Node(int a)
{
	ground=a;
	fx=gx=hx=0;
}
int Node::cal_hx(int x, int y)
{
	hx=abs(x-pos.x)*10+abs(y-pos.y)*10;
	return hx;
}
int Node::cal_fx()
{
	fx=gx+hx;
	return fx;
}

/////////// Vector ////////////////
Vector::Vector(double x1, double y1)
{
	x=x1;  y=y1;
}
Vector::Vector(const Vector& a)
{
	x=a.x;   y=a.y;
}
Vector::Vector() 
{
	x=0;  y=0;
}
Vector::Vector(POINT a , POINT b)
{
	x=b.x-a.x; y=b.y-a.y;
}
Vector Vector::vertical()  //把向量变成其垂直向量
{
	double tem=x; x=y; y=-tem;
	return *this;
} 
double Vector::get_lenth()
{
	return sqrt(x*x+y*y);
}
Vector Vector::new_normalize()
{
	double a=get_lenth();
	x/=a; y/=a;
	return *this;
}
double Vector::dotmulti(Vector a)
{
	return a.x*x+a.y*y;
}
Vector Vector::operator = (Vector a)
{
	x=a.x; y=a.y;
	return *this;
}
Vector Vector::operator - (Vector a)
{
	temp_vector.x=x-a.x; temp_vector.y=y-a.y;
	return temp_vector;
}
Vector Vector::operator + (Vector a)
{
	temp_vector.x=x+a.x; temp_vector.y=y+a.y;
	return temp_vector;
}
Vector Vector::operator * (double a)
{
	temp_vector.x=x*a; temp_vector.y=y*a;
	return temp_vector;
}
Vector Vector::operator / (double a)
{
	temp_vector.x=x/a; temp_vector.y=y/a;
	return temp_vector;
}

/////////// Game ////////////////
Game::Game()
{
	startup();
}
void Game::startup()
{
	memset(mapp,0,sizeof(mapp));
	for(int i=0; i<=42; i++)
	{
		for(int j=0; j<=42; j++)
		{	
			mapp[i][j].pos.x=i;
			mapp[i][j].pos.y=j;
		}
	}
	death_count=0;  // 杀怪计数
	judge_update=0;
	room_count=1;
	room.new_room(room_count);   // 通过房间计数，用于升级
}
void Game::clear()
{
	setfillcolor(BLACK); setlinecolor(BLACK);
	fillrectangle(0,0,1500,990);
	return;
}
void Game::show()
{
	ben.print_cha_new(ben.pos_x,ben.pos_y,ben.print_chara);
	if(room.time_count<room.time_max)
		square.paint_room_new(square.pos_x,square.pos_y,square.pos,square.angle);
	for(int i=0; i<room.num_stab; i++)
	{	
		room.stab[i].count++;
		double c;
		switch(square.jud_way)
		{
		case 1: c=square.speed/100; break;
		case 2: c=-square.speed/100; break;
		default: c=0;
		}
		room.stab[i].print_now(c);
		if(room.stab[i].count>room.stab[i].count_max)
		{	room.stab[i].judge_show=!room.stab[i].judge_show;
			room.stab[i].count=0;
		}
	} 
	for(int i=0; i<room.num_stone; i++)
	{	
		double c;
		switch(square.jud_way)
		{
		case 1: c=square.speed/100; break;
		case 2: c=-square.speed/100; break;
		default: c=0;
		}
		room.stone[i].print_now(c);
	}
	square.jud_way=0;
	int x=150,y=200,co=0;
	//  print life  //
	putimage(x,y,&img_empt);
	for(int i=1; i<=ben.life_now/2; i++)
	{
		putimage(x,y,&img_heart1);
		x+=45; 
		co++;
	}
	if(ben.life_now%2==1)
	{
		putimage(x,y,&img_heart2);
		x+=45;
		co++;
	}
	for(int i=0; i<ben.life/2-co; i++)
	{
		putimage(x,y,&img_heart3);
		x+=45;
	}
	LOGFONT f;
	gettextstyle(&f); 
	f.lfHeight = 40;  
	f.lfWidth=25;
	_tcscpy(f.lfFaceName, _T("黑体"));   
	f.lfQuality = ANTIALIASED_QUALITY;  
	settextstyle(&f);            

	switch(ben.mod)
	{
	case 1: putimage(50,170,&img_cha1); outtextxy(170,140,_T("Benzene")); break;
	case 2: putimage(50,170,&img_cha2); outtextxy(150,140,_T("Cyclohexadiene")); break;
	case 3: putimage(50,170,&img_cha3); outtextxy(170,140,_T("Pyran")); break;
	}
	int x1=80,x2=240;
	y=350;
	switch(ben.ski[0])
	{
	case 1: putimage(x1,y,&img_ski1); break;
	case 2: putimage(x1,y,&img_ski2); break;
	case 3: putimage(x1,y,&img_ski3); break;
	case 4: putimage(x1,y,&img_ski4); break;
	case 5: putimage(x1,y,&img_ski5); break;
	case 6: putimage(x1,y,&img_ski6); break;
	}
	switch(ben.ski[1])
	{
	case 0: putimage(x2,y,&img_ski_null); break;
	case 1: putimage(x2,y,&img_ski1); break;
	case 2: putimage(x2,y,&img_ski2); break;
	case 3: putimage(x2,y,&img_ski3); break;
	case 4: putimage(x2,y,&img_ski4); break;
	case 5: putimage(x2,y,&img_ski5); break;
	case 6: putimage(x2,y,&img_ski6); break;
	}
	setlinestyle(PS_SOLID, 5); setlinecolor(RGB(0,0,0));
	line(x2,y,x2+100,y);
	line(x2+100,y,x2+100,y+100);
	line(x2+100,y+100,x2,y+100);
	line(x2,y+100,x2,y);
	line(x1,y,x1+100,y);
	line(x1+100,y,x1+100,y+100);
	line(x1+100,y+100,x1,y+100);
	line(x1,y+100,x1,y);
	setlinestyle(PS_SOLID, 5); setlinecolor(RGB(255,255,0));
	if(ben.cur==0 || ben.cur==2) 
		x=x1;
	else
		x=x2;
	line(x,y,x+100,y);
	line(x+100,y,x+100,y+100);
	line(x+100,y+100,x,y+100);
	line(x,y+100,x,y);

	putimage(80,350+300,&img_coin2);
	putimage(80,350+400,&img_coin1);
	f.lfHeight = 35;  
	f.lfWidth=20;
	settextstyle(&f);   
	TCHAR s1[10]; 
	_stprintf(s1,_T("灵魂：%d"),death_count);
	outtextxy(80+100,350+320,s1);
	_stprintf(s1,_T("金币：%d"),room_count+coin-1);
	outtextxy(80+100,350+420,s1);
//	square.tester();
//	square.paint_room_new(square.pos_x,square.pos_y,square.pos,square.angle);
}
void Game::print_new()
{
	clear();
	square.paint_room_new(square.pos_x,square.pos_y,square.pos,square.angle);
	ben.print_cha_new(ben.pos_x,ben.pos_y, ben.print_chara);
}
void Game::updateWithoutInput()
{
	room.time_count++;
	Bullet::num_time_count++;
	judge_coll_cha_to_mon();
	judge_coll_mon_to_mon();
	judge_coll_chara_to_wall();
	judge_coll_cha_to_obstacle();
	judge_coll_mon_to_wall();
	judge_coll_mon_to_obstacle();
	
	//////// update ///////////
	update_bullet();
	ben.update();
	fresh_map();
	room.update_monster(ben.pos_x, ben.pos_y, square);
	fresh_room();
}
void Game::update_bullet()
{
	if(  room.time_count>=room.time_max )
		ben.cur-=2;
//	if(ben.ski[ben.cur]==1)
	{
		if(ben.last!=ben.head)
		{
			Bullet *bul=ben.head->nex,*pre_bul=ben.head;
			while(bul!=NULL)
			{
				bul->life++;
				if(bul->life>=Bullet::range[bul->cur])
				{	
					bul->exist=false;
					ben.num_bul--;
				}
				if(bul->exist==true)
				{
					if( ( (bul->pos_x-square.pos_x)*(bul->pos_x-square.pos_x)  )+( (bul->pos_y-square.pos_y)*(bul->pos_y-square.pos_y) )>=350*350*2  )
					{	
						bul->exist=false;
						ben.num_bul--;
					}
					bul->print_bul_old(bul->pos_x,bul->pos_y);
					bul->pos_x+=bul->speed[bul->cur]*cosf(bul->xita);
					bul->pos_y-=bul->speed[bul->cur]*sinf(bul->xita);
					bul->print_bul_new(bul->pos_x,bul->pos_y);
					judge_bullet(5,8,square.pos,bul->pos_x, bul->pos_y, bul->xita);
					Vector circle_up(bul->pos_x-bul->r,bul->pos_y-bul->r),circle_down(bul->pos_x+bul->r,bul->pos_y+bul->r);
					for(int i=0; i<400; i++)
						if(room.monster[i].exist==true)
							if( judge_circle_coll(circle_up,circle_down,room.monster[i].pos,room.monster[i].num_edge)==true  )
							{	
								bul->exist=false;
								ben.num_bul--;
								room.monster[i].print_old(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
								room.monster[i].num_edge--;
								if(room.monster[i].num_edge<3)
								{	
									room.monster[i].exist=false;
									if(room.monster[i].special==0)
										death_count++;
									else
										death_count+=3;
									Monster::num_total--;
								}
								if(room.monster[i].exist!=false)
									room.monster[i].print_now(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
							}
				}
				else
				{
					bul->print_bul_old(bul->pos_x,bul->pos_y);
					if(bul->nex!=NULL)
					{	
						pre_bul->nex=bul->nex;
						if(bul!=NULL)
							delete bul;
						bul=pre_bul->nex;
						continue;
					}
				}
				pre_bul=pre_bul->nex;
				bul=bul->nex;
			}
		}
/*
		if(ben.head->nex==NULL)
		{	
			ben.head->nex=ben.last;
			ben.last->nex=NULL;
		}*/
	}
	if(ben.ski[ben.cur]==3 || ben.ski[ben.cur]==4)
	{
		if(ben.last_line.exist==true)
		{
			if(Bullet::num_time_count>3)
				ben.last_line.exist=false;
		}
		if( (ben.last_line.exist==false&&Bullet::num_time_count!=3) ) return;
		ben.line=ben.last_line;
		POINT line1_head,line1_last,line2_head,line2_last;
		POINT tem,cut,tttem; 
		line1_head.x=ben.line.pos_x;
		line1_head.y=ben.line.pos_y;
		while(ben.line.life>0)
		{
			tem.x=line1_head.x+ben.line.life*cosf(ben.line.xita);
			tem.y=line1_head.y-ben.line.life*sinf(ben.line.xita);
			line1_last=tem;
			if(ben.ski[ben.cur]==3&&ben.line.exist==true&&Bullet::num_time_count==1)
			{
				for(int j=0; j<400; j++)
				if(room.monster[j].exist==true)
				{
					for(int k=0; k<room.monster[j].num_edge; k++)
					{
						if(judge_coll_line(line1_head,line1_last,room.monster[j].pos[k],room.monster[j].pos[k+1],tttem)==true)
						{
							room.monster[j].print_old(room.monster[j].pos_x,room.monster[j].pos_y,room.monster[j].num_edge,room.monster[j].pos);
							room.monster[j].num_edge--;
							if(room.monster[j].num_edge<3)
							{	
								room.monster[j].exist=false;
								if(room.monster[j].special==0)
									death_count++;
								else
									death_count+=3;
								Monster::num_total--;
							}
							if(room.monster[j].exist!=false)
								room.monster[j].print_now(room.monster[j].pos_x,room.monster[j].pos_y,room.monster[j].num_edge,room.monster[j].pos);
						}
					}
				}
			}
			else if(ben.ski[ben.cur]==4) // 即死激光反弹函数区
			{
				if(Bullet::num_time_count==3)
					Game::clear();
					double minx=MAX_DOUBLE;
					for(int j=0; j<400; j++) // 找激光可射中的最近的怪物的距离平方最小值
					{
						if(room.monster[j].exist==false) continue;
						for(int k=0; k<room.monster[j].num_edge; k++)
							if(judge_coll_line(line1_head,line1_last,room.monster[j].pos[k],room.monster[j].pos[k+1],cut)==true)
								if( !(abs(cut.x-line1_head.x)<2&&abs(cut.y-line1_head.y)<2)&& !(abs(cut.x-line1_last.x)<2&&abs(cut.y-line1_last.y)<2))
								{	
									minx=min(minx, (line1_head.x-room.monster[j].pos_x)*(line1_head.x-room.monster[j].pos_x)+(line1_head.y-room.monster[j].pos_y)*(line1_head.y-room.monster[j].pos_y)  );
									break;
								}
					}
					for(int j=0; j<room.num_stone; j++) // 找激光可射中的最近的岩石的距离平方最小值
					{
						for(int k=0; k<4; k++)
							if(judge_coll_line(line1_head,line1_last,room.stone[j].pos[k],room.stone[j].pos[k+1],cut)==true)
								if( !(abs(cut.x-line1_head.x)<2&&abs(cut.y-line1_head.y)<2)&& !(abs(cut.x-line1_last.x)<2&&abs(cut.y-line1_last.y)<2))
								{	
									minx=min(minx, (line1_head.x-room.stone[j].pos_x)*(line1_head.x-room.stone[j].pos_x)+(line1_head.y-room.stone[j].pos_y)*(line1_head.y-room.stone[j].pos_y)  );
									break;
								}
					}

					int j=0;
					for( ;j<400; j++) //找激光可射中的最近的怪物
						if(room.monster[j].exist==true)
						{
							if(minx!=(line1_head.x-room.monster[j].pos_x)*(line1_head.x-room.monster[j].pos_x)+(line1_head.y-room.monster[j].pos_y)*(line1_head.y-room.monster[j].pos_y))
								continue;
							double minx1=MAX_DOUBLE;
							for(int k=0; k<room.monster[j].num_edge; k++) // 找该怪物距离出射点最近的一条边并记录最小值
							{
								minx1=min(minx1,point_to_line(line1_head,room.monster[j].pos[k],room.monster[j].pos[k+1]));
							}
							int k=0;
							for(; k<room.monster[j].num_edge; k++)
							{
								if(minx1!=point_to_line(line1_head,room.monster[j].pos[k],room.monster[j].pos[k+1])) continue;
								judge_coll_line(line1_head,line1_last,room.monster[j].pos[k],room.monster[j].pos[k+1],cut);
								if(ben.line.exist==true && Bullet::num_time_count==2)
								{	
									room.monster[j].print_old(room.monster[j].pos_x,room.monster[j].pos_y,room.monster[j].num_edge,room.monster[j].pos);
									room.monster[j].exist=false;
									Monster::num_total--;
									//printf("1111\n");
									if(room.monster[j].special==0)
										death_count++;
									else
										death_count+=3;
								}
								setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 0 , 255 , 0 ));
								if(Bullet::num_time_count==3)
								{
									setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 0 , 0 , 0 ));
								}
								if(Bullet::num_time_count==1)
									line(line1_head.x,line1_head.y, cut.x, cut.y);
								ben.line.life-=sqrt( (ben.line.pos_x-cut.x)*(ben.line.pos_x-cut.x)  + (ben.line.pos_y-cut.y)*(ben.line.pos_y-cut.y) );
								judge_bullet(k,k+1,room.monster[j].pos,cut.x, cut.y, ben.line.xita);
								line1_head.x=cut.x; line1_head.y=cut.y;
								break;
							}
						if(k<room.monster[j].num_edge) break;
					}
					
					int q=0;
					for( ;q<room.num_stone; q++) //找激光可射中的最近的岩石
					{
						if(minx!=(line1_head.x-room.stone[q].pos_x)*(line1_head.x-room.stone[q].pos_x)+(line1_head.y-room.stone[q].pos_y)*(line1_head.y-room.stone[q].pos_y))
							continue;
						double minx1=MAX_DOUBLE;
						for(int k=0; k<4; k++) // 找该岩石距离出射点最近的一条边并记录最小值
						{
							minx1=min(minx1,point_to_line(line1_head,room.stone[q].pos[k],room.stone[q].pos[k+1]));
						}
						int k=0;
						for(; k<4; k++)
						{
							if(minx1!=point_to_line(line1_head,room.stone[q].pos[k],room.stone[q].pos[k+1])) continue;
							judge_coll_line(line1_head,line1_last,room.stone[q].pos[k],room.stone[q].pos[k+1],cut);
							setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 0 , 255 , 0 ));
							if(Bullet::num_time_count==3)
							{
								setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 0 , 0 , 0 ));
							}
							if(Bullet::num_time_count==1)
								line(line1_head.x,line1_head.y, cut.x, cut.y);
							ben.line.life-=sqrt( (ben.line.pos_x-cut.x)*(ben.line.pos_x-cut.x)  + (ben.line.pos_y-cut.y)*(ben.line.pos_y-cut.y) );
							judge_bullet(k,k+1,room.stone[q].pos,cut.x, cut.y, ben.line.xita);
							line1_head.x=cut.x; line1_head.y=cut.y;
							break;
						}
						if(k<4) break;
					}
					if(q<room.num_stone || j<400) continue;

			}
			int i=0; // 墙壁反射
			for(; i<4; i++)
			{
				if(i==0)
				{	line2_head=square.edge1[0]; line2_last=square.edge1[1]; }
				if(i==1)
				{	line2_head=square.edge2[0];line2_last=square.edge2[1]; }
				if(i==2)
				{	line2_head=square.edge3[0]; line2_last=square.edge3[1]; }
				if(i==3)
				{	line2_head=square.edge4[0]; line2_last=square.edge4[1]; }
				if(judge_coll_line(line1_head,line1_last,line2_head,line2_last,cut)==true)
				{
					if( !(abs(cut.x-line1_head.x)<2&&abs(cut.y-line1_head.y)<2)&& !(abs(cut.x-line1_last.x)<2&&abs(cut.y-line1_last.y)<2))
					{
						if(ben.ski[ben.cur]==3)
						{
							setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 255 , 0 , 0 ));
						}
						else
						{
							setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 0 , 255 , 0 ));
						}
						if(Bullet::num_time_count==3)
						{
							setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 0 , 0 , 0 ));
						}
						if( ( Bullet::num_time_count==1 && ben.ski[ben.cur]==4 ) || ben.ski[ben.cur]==3)
							line(line1_head.x,line1_head.y, cut.x, cut.y);
						ben.line.life-=sqrt( (ben.line.pos_x-cut.x)*(ben.line.pos_x-cut.x)  + (ben.line.pos_y-cut.y)*(ben.line.pos_y-cut.y) );
						judge_bullet(5,8,square.pos,cut.x, cut.y, ben.line.xita);
						line1_head.x=cut.x; line1_head.y=cut.y;
						break;
					}
				}
			}
			if(i<4) continue; 
			// 与墙壁也没发生反射 激光直射至射程最大值
			if(ben.ski[ben.cur]==3)
			{
				setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 255 , 0 , 0 ));
			}
			else
			{
				setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 0 , 255 , 0 ));
			}
			if( ( Bullet::num_time_count==1 && ben.ski[ben.cur]==4 ) || ben.ski[ben.cur]==3)
				line ( line1_head.x , line1_head.y , line1_last.x , line1_last.y );
			if(ben.ski[ben.cur]==3)
			{
				if(Bullet::num_time_count==3)
				{
					setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 0 , 0 , 0 ));
				}
				line ( line1_head.x , line1_head.y , line1_last.x , line1_last.y );
			}
			break;
		}
		ben.line.life=0;
		
	}

	if(ben.ski[ben.cur]==5) // bomb
	{
		if(ben.num_bul==0) return;
		ben.head->life++;
		if(ben.head->life==Bullet::range[ben.head->cur])
		{	
			ben.head->exist=false;
			ben.num_bul=0;
			ben.head->print_bul_old(ben.head->pos_x,ben.head->pos_y);
			bomb_hurt(1);
		}
		if(ben.head->exist==true)
		{
			if( ( (ben.head->pos_x-square.pos_x)*(ben.head->pos_x-square.pos_x)  )+( (ben.head->pos_y-square.pos_y)*(ben.head->pos_y-square.pos_y) )>=350*350*2  )
				ben.head->exist=false;
			ben.head->print_bul_old(ben.head->pos_x,ben.head->pos_y);
			ben.head->pos_x+=ben.head->speed[ben.head->cur]*cosf(ben.head->xita);
			ben.head->pos_y-=ben.head->speed[ben.head->cur]*sinf(ben.head->xita);
			ben.head->print_bul_new(ben.head->pos_x,ben.head->pos_y);
			judge_bullet(5,8,square.pos,ben.head->pos_x, ben.head->pos_y, ben.head->xita);
			Vector circle_up(ben.head->pos_x-ben.head->r,ben.head->pos_y-ben.head->r),circle_down(ben.head->pos_x+ben.head->r,ben.head->pos_y+ben.head->r);
			for(int i=0; i<400; i++)
				if(room.monster[i].exist==true)
					if( judge_circle_coll(circle_up,circle_down,room.monster[i].pos,room.monster[i].num_edge)==true  )
					{	
						ben.head->exist=false;
						ben.num_bul=0;
						ben.head->print_bul_old(ben.head->pos_x,ben.head->pos_y);
						room.monster[i].print_old(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
						room.monster[i].exist=false;
						if(room.monster[i].special==0)
							death_count++;
						else
							death_count+=3;
						Monster::num_total--;
						bomb_hurt(1);
						break;
					}
		}
	}
	if(  room.time_count>=room.time_max )
	{	
		ben.cur+=2;
		return ;
	}
	if(ben.ski[ben.cur]==6) // float
	{
		ben.special.print_bul_new(ben.special.pos_x,ben.special.pos_y);
		Vector circle_up(ben.special.pos_x-ben.special.r,ben.special.pos_y-ben.special.r),circle_down(ben.special.pos_x+ben.special.r,ben.special.pos_y+ben.special.r);
		judge_bullet(5,8,square.pos,ben.special.pos_x, ben.special.pos_y, ben.special.xita);
		for(int i=0; i<400; i++)
			if(room.monster[i].exist==true)
				if( judge_circle_coll(circle_up,circle_down,room.monster[i].pos,room.monster[i].num_edge)==true  )
				{	
					room.monster[i].print_old(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
					room.monster[i].exist=false;
					if(room.monster[i].special==0)
						death_count++;
					else
						death_count+=3;
					Monster::num_total--;
					ben.special.r+=7;
					ben.special.speed[ben.special.cur]-=2;
					if(ben.special.r>=50)
					{
						ben.last_special.pos_x=ben.special.pos_x;
						ben.last_special.pos_y=ben.special.pos_y;
						ben.special.r=20;
						ben.special.speed[ben.special.cur]=22;
						bomb_hurt(2);
						break;
					}
				}
	}
	return;
}
void Game::updateWithInput()
{
	if((GetAsyncKeyState('W')<0)||(GetAsyncKeyState('S')<0)|| (GetAsyncKeyState('A')<0) ||(GetAsyncKeyState('D')<0))
	{
		double old_x=ben.pos_x,old_y=ben.pos_y;
		ben.print_cha_old(ben.pos_x,ben.pos_y,ben.print_chara);
		if(GetAsyncKeyState('W')<0) 
			ben.pos_y=old_y-ben.speed;
		if(GetAsyncKeyState('S')<0) 
			ben.pos_y=old_y+ben.speed; 
		if(GetAsyncKeyState('A')<0) 
			ben.pos_x=old_x-ben.speed;
		if(GetAsyncKeyState('D')<0) 
			ben.pos_x=old_x+ben.speed; 
		ben.print_cha_new(ben.pos_x,ben.pos_y,ben.print_chara);	
	}
	square.judge_input(ben.ski[ben.cur]);
	if(room.time_count>=room.time_max) return;
	ben.updateWithInput(ben.pos_x, ben.pos_y,ben.print_chara);
	if(_kbhit()) 
	{	
		char order=_getch();
		if(order=='q')
		{
			{
				if(ben.last!=ben.head)
				{
					Bullet *bul=ben.head->nex,*pre_bul=ben.head;
					ben.head->print_bul_old(ben.head->pos_x,ben.head->pos_y);
					ben.head->exist=false;
					while(bul!=NULL)
					{
						bul->exist=false;
						{
							bul->print_bul_old(bul->pos_x,bul->pos_y);
							if(bul->nex!=NULL)
							{	
								pre_bul->nex=bul->nex;
								if(bul!=NULL)
									delete bul;
								bul=pre_bul->nex;
								continue;
							}
						}
						pre_bul=pre_bul->nex;
						bul=bul->nex;
					}
				}
				if(ben.head->nex==NULL)
				{	
					ben.head->nex=ben.last;
					ben.last->nex=NULL;
				}
			}
			if(ben.ski[1-ben.cur]==0) return;
			else ben.cur=1-ben.cur;
			if(ben.ski[ben.cur]==2)
			{
				for(int i=0; i<Monster::num_count; i++)
				{	
					if(room.monster[i].exist=false) continue; 
					room.monster[i].exist=false;
					Monster::num_total--;
					room.monster[i].print_old(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
				}
				ben.num_count[2]++;
			}
			if(ben.ski[ben.cur]==5)
			{
				ben.special.print_bul_old(ben.special.pos_x,ben.special.pos_y);
				ben.num_bul=0;
				ben.special.exist=false;
				ben.special.r=5;
			}
			if(ben.ski[ben.cur]==6)
			{
				ben.special.pos_x=ben.pos_x;
				ben.special.pos_y=ben.pos_y;
				ben.last_special.exist=false;
				ben.last_special.r=30;
				ben.last_special.special=true;
				ben.special.r=20;
				ben.special.exist=true;
				ben.special.special=true;
			}
			ben.print_part_cha_new(ben.pos_x,ben.pos_y,ben.print_chara);
		}
	}
}
void Game::judge_bullet(int start, int end, POINT pos[], double x, double y, double &xita)
{
	for(int i=start; i<=end; i++)
	{
		int j=i+1;
		double k=(pos[i].y*1.0-pos[j].y*1.0)/(pos[i].x*1.0-pos[j].x*1.0);
		double b=pos[i].y*1.0-k*pos[i].x;
		double c=k*x*1.0+b-y*1.0;
		double d=abs(c*1.0)/sqrt(k*k+1);
		if( abs(pos[i].y-pos[j].y)<2 )
			d=abs(y-pos[i].y);
		if( abs(pos[i].x-pos[j].x)<2 )
			d=abs(x-pos[i].x);
		if(d<10)
		{
			if(abs(k)<1e-6|| abs(pos[i].x*1.0-pos[j].x*1.0)<2|| abs(pos[i].y*1.0-pos[j].y*1.0)<2) {xita=pi+xita; return;}
			if( !( (x<=max(pos[i].x,pos[j].x))&&(x>=min(pos[i].x,pos[j].x))&&(y<=max(pos[i].y,pos[j].y))&&(y>=min(pos[i].y,pos[j].y))))
				return; 
			double linex=pos[i].x*1.0-pos[j].x*1.0,liney=pos[i].y*1.0-pos[j].y*1.0;
			double ix=cosf(xita),iy=sinf(xita);
			if(abs(linex)<1e-6) {liney=1.0; linex=0.0;}
			else {liney/=linex; linex=-1.0;}
			double tem=sqrt(ix*ix+iy*iy),angle=0;
			if(abs(tem)<1e-6)  angle=0;
			else
			{
				angle=asinf(iy/tem);
				if(ix>1e-6)
				{
					if(iy>1e-6) angle=angle;
					else angle=angle+pi2;
				}
				else
					angle=pi-angle;
			}
			 tem=sqrt(linex*linex+liney*liney);
			 double angle1=0;
			if(abs(tem)<1e-6)  angle1=0;
			else
			{
				angle1=asinf(liney/tem);
				if(linex>1e-6)
				{
					if(liney>1e-6) angle1=angle1;
					else angle1=angle1+pi2;
				}
				else
					angle1=pi-angle1;
			}
			xita=2*angle1-angle;
			return;
		}
	}
}
bool Game::judge_coll_chara_to_wall()
{
	Vector shadow;
	double num_move=0;
	int flag=0;
	if(judge_coll_single(ben.print_chara,7,square.edge1,5,shadow,num_move)==true)
	{	
		ben.print_cha_old(ben.pos_x,ben.pos_y,ben.print_chara);
		ben.pos_x-=shadow.x*(num_move+5);
		ben.pos_y-=shadow.y*(num_move+5);
		ben.print_cha_new(ben.pos_x,ben.pos_y,ben.print_chara);
		flag=1;
		//return true;
	}
	//	printf("Collision!  %d\n", ++count);
	if(judge_coll_single(ben.print_chara,7,square.edge2,5,shadow,num_move)==true)
	{	
		ben.print_cha_old(ben.pos_x,ben.pos_y,ben.print_chara);
		ben.pos_x-=shadow.x*(num_move+5);
		ben.pos_y-=shadow.y*(num_move+5);
		ben.print_cha_new(ben.pos_x,ben.pos_y,ben.print_chara);
		flag=1;
	//	return true;
	}
	//	printf("Collision!  %d\n", ++count);
	if(judge_coll_single(ben.print_chara,7,square.edge3,5,shadow,num_move)==true)
	{	
		ben.print_cha_old(ben.pos_x,ben.pos_y,ben.print_chara);
		ben.pos_x-=shadow.x*(num_move+5);
		ben.pos_y-=shadow.y*(num_move+5);
		ben.print_cha_new(ben.pos_x,ben.pos_y,ben.print_chara);
		flag=1;
	//	return true;
	}
	//	printf("Collision!  %d\n", ++count);
	if(judge_coll_single(ben.print_chara,7,square.edge4,5,shadow,num_move)==true)
	{	
		ben.print_cha_old(ben.pos_x,ben.pos_y,ben.print_chara);
		ben.pos_x-=shadow.x*(num_move+5);
		ben.pos_y-=shadow.y*(num_move+5);
		ben.print_cha_new(ben.pos_x,ben.pos_y,ben.print_chara);
		flag=1;
	//	return true;
	}
	return flag==1;
}
void Game::judge_coll_mon_to_wall()
{
	Vector shadow;
	for(int i=0; i<400; i++)
		if(room.monster[i].exist)
		{
			double num_move=0;
			if(judge_coll_single(room.monster[i].pos,room.monster[i].num_edge,square.edge1,5,shadow,num_move)==true)
			{	
				room.monster[i].print_old(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
				room.monster[i].pos_x-=shadow.x*num_move;
				room.monster[i].pos_y-=shadow.y*num_move;
				room.monster[i].print_now(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
			}
			if(judge_coll_single(room.monster[i].pos,room.monster[i].num_edge,square.edge2,5,shadow,num_move)==true)
			{	
				room.monster[i].print_old(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
				room.monster[i].pos_x-=shadow.x*num_move;
				room.monster[i].pos_y-=shadow.y*num_move;
				room.monster[i].print_now(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
			}
			if(judge_coll_single(room.monster[i].pos,room.monster[i].num_edge,square.edge3,5,shadow,num_move)==true)
			{	
				room.monster[i].print_old(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
				room.monster[i].pos_x-=shadow.x*num_move;
				room.monster[i].pos_y-=shadow.y*num_move;
				room.monster[i].print_now(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
			}
			if(judge_coll_single(room.monster[i].pos,room.monster[i].num_edge,square.edge4,5,shadow,num_move)==true)
			{
				room.monster[i].print_old(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
				room.monster[i].pos_x-=shadow.x*num_move;
				room.monster[i].pos_y-=shadow.y*num_move;
				room.monster[i].print_now(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
			}
			judge_coll_mon_to_corner(i);
			if( ( (room.monster[i].pos_x-square.pos_x)*(room.monster[i].pos_x-square.pos_x)  )+( (room.monster[i].pos_y-square.pos_y)*(room.monster[i].pos_y-square.pos_y) )>=350*350*2  )
			{	
				room.monster[i].exist=false;
				Monster::num_total--;
				room.monster[i].print_old(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
			}
		}
	return ;
}
void Game::judge_coll_cha_to_mon()
{
	Vector shadow;
	for(int i=0; i<400; i++)
		if(room.monster[i].exist)
		{
			double num_move=0;
			if(judge_coll_single(room.monster[i].pos,room.monster[i].num_edge,ben.print_chara,7,shadow,num_move)==true)
			{	
				room.monster[i].print_old(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
				room.monster[i].pos_x-=shadow.x*num_move;
				room.monster[i].pos_y-=shadow.y*num_move;
				room.monster[i].print_now(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
				if(ben.judge_hurt==-1)
				{
					ben.judge_hurt++;
					ben.life_now--;
					room.monster[i].print_old(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
					room.monster[i].num_edge--;
					if(room.monster[i].num_edge<3)
					{	
						room.monster[i].exist=false;
						if(room.monster[i].special==1)
							death_count+=10;
						Monster::num_total--;
					}
					if(room.monster[i].exist!=false)
						room.monster[i].print_now(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
				}
			}
		}
	return ;
}
void Game::judge_coll_mon_to_mon()
{
	Vector shadow;
	for(int i=0; i<400; i++)
	{
		if(room.monster[i].special==3) continue;
		if(room.monster[i].exist)
			for(int j=i+1; j<400; j++)
				if(room.monster[j].exist)
				{
					if(room.monster[j].special==3) continue;
					double num_move=0;
					if(judge_coll_single(room.monster[i].pos,room.monster[i].num_edge,room.monster[j].pos,room.monster[j].num_edge,shadow,num_move)==true)
					{	
						room.monster[i].print_old(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
						//room.monster[j].print_now(room.monster[j].pos_x,room.monster[j].pos_y,room.monster[j].num_edge,room.monster[j].pos);
						room.monster[i].pos_x-=shadow.x*num_move;
						room.monster[i].pos_y-=shadow.y*num_move;
						room.monster[i].print_now(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
					}
				}
	}
	return ;
}
void Game::judge_coll_corner(double& pos_x,double& pos_y, POINT second[], int num_second ,double center_x,double center_y)
{
	Vector hori(1,0);
	for(int i=0; i<num_second; i++)
	{
		double tem=sqrt( (pos_x-second[i].x)*(pos_x-second[i].x) + (pos_y-second[i].y)*(pos_y-second[i].y) );
		if( tem<50  )
		{
			Vector a(center_x-second[i].x,center_y-second[i].y);
			double xita=acosf( (a.x-hori.x) / a.get_lenth());
			pos_x+=tem*(cosf(xita));
			pos_y-=tem*(sinf(xita));
		}
	}
	return;
}
void Game::judge_coll_cha_to_obstacle()
{
	Vector shadow;
	double num_move=0;
	for(int i=0; i<room.num_stone; i++)
		if(judge_coll_single(ben.print_chara,7,room.stone[i].pos,5,shadow,num_move)==true)
		{	
			ben.print_cha_old(ben.pos_x,ben.pos_y,ben.print_chara);
			ben.pos_x-=shadow.x*(num_move);
			ben.pos_y-=shadow.y*(num_move);
			ben.print_cha_new(ben.pos_x,ben.pos_y,ben.print_chara);
		}
	for(int i=0; i<room.num_stab; i++)
		if(judge_coll_single(ben.print_chara,7,room.stab[i].pos,5,shadow,num_move)==true)
		{	
			if(ben.judge_hurt==-1)
			{
				ben.judge_hurt++;    
				ben.life_now--;
			}
		}
	return;
}
void Game::judge_coll_mon_to_corner(int i)
{
	room.monster[i].print_old(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
	judge_coll_corner(room.monster[i].pos_x,room.monster[i].pos_y, square.corner, 4, square.pos_x, square.pos_y);
	room.monster[i].print_now(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
	return;
}
void Game::judge_coll_mon_to_obstacle()
{
	Vector shadow; double num_move;
	for(int i=0; i<400; i++)
	{	
		if(room.monster[i].exist==false) continue;
		for(int j=0; j<room.num_stab; j++)
		{
			if(room.monster[i].special==1) break;
			if(room.stab[j].judge_show==false) continue;
			if(judge_coll_single(room.monster[i].pos,room.monster[i].num_edge, room.stab[j].pos ,5,shadow,num_move)==true)
			{	
				room.monster[i].print_old(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
				room.monster[i].num_edge--;
				if(room.monster[i].num_edge<3)
				{	
					if(ben.cur==2 || ben.cur==3 || ben.ski[ben.cur]==2)
					{
						if(room.monster[i].special==0)
							death_count+=2;
						else
							death_count+=5;
					}
					room.monster[i].exist=false;
					Monster::num_total--;
				}
				if(room.monster[i].exist!=false)
					room.monster[i].print_now(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
			}
		}
		for(int j=0; j<room.num_stone; j++)
		{
			if(room.monster[i].special==2) break;
			if(judge_coll_single(room.monster[i].pos,room.monster[i].num_edge, room.stone[j].pos ,5,shadow,num_move)==true)
			{	
				room.monster[i].print_old(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
				room.monster[i].pos_x-=shadow.x*(num_move+5);
				room.monster[i].pos_y-=shadow.y*(num_move+5);
				room.monster[i].print_now(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
			}
		}
	}
}
void Game::fresh_map()
{
	memset(mapp,0,sizeof(mapp));
	for(int i=0; i<42; i++)   // 实时更新mapp
		for(int j=0; j<42; j++)
		{
			POINT p={ i,j };
			mapp[i][j].pos=p;
			mapp[i][j].cal_hx(get_i(normalize_x(ben.pos_x)), get_j(normalize_y(ben.pos_y)));
			mapp[i][j].ground=0;
		}
		// 设置地图标识号
	for(int i=0; i<room.num_stab; i++)
	{
		int tem_x=get_i(normalize_x(room.stab[i].pos_x)),tem_y=get_j(normalize_y(room.stab[i].pos_y));
	//	mapp[tem_x][tem_y].ground=1;
		for(int j=tem_x-1; j<=tem_x+1; j++)
			for(int k=tem_y-1; k<=tem_y+1; k++)
			{
		//		if(j==tem_x&& k==tem_y) continue;
				mapp[j][k].ground|=(1<<4);
				mapp[j][k].ground|=(1<<0);
			}
	}
	for(int i=0; i<room.num_stone; i++)
	{
		int tem_x=get_i(normalize_x(room.stone[i].pos_x)),tem_y=get_j(normalize_y(room.stone[i].pos_y));
		mapp[tem_x][tem_y].ground|=(1<<3);
		mapp[tem_x][tem_y].ground|=(1<<0);
		for(int j=tem_x-1; j<=tem_x+1; j++)
			for(int k=tem_y-1; k<=tem_y+1; k++)
			{
				if(j==tem_x&& k==tem_y) continue;
				if( ( (mapp[j][k].ground>>3) & (1) )==1 )
				{	
					mapp[j][k].ground|=(1<<0);
					continue;
				}
				else if(( (mapp[j][k].ground>>2) & (1) )==1)
				{	
					mapp[j][k].ground|=(1<<3);
					mapp[j][k].ground|=(1<<0);
					continue;
				}
				else
					mapp[j][k].ground|=(1<<2);
			}
	}
	int tem_ben_x=get_i(normalize_x(ben.pos_x)),tem_ben_y=get_j(normalize_y(ben.pos_y));
	mapp[tem_ben_x][tem_ben_y].ground|=(1<<1);
	for(int i=tem_ben_x-1; i<=tem_ben_x+1; i++)
		for(int j=tem_ben_y-1; j<=tem_ben_y+1; j++)
			mapp[i][j].ground=mapp[i][j].ground%2==0?mapp[i][j].ground:mapp[i][j].ground-1;
	return ;
}
void Game::fresh_room()
{
	if(room.time_count==room.time_max) 
	{	
/*		if( !(ben.mod==3&&ben.judge_cha_state==1) )*/
		if(ben.ski[ben.cur]!=6)
			ben.head->print_bul_old(ben.head->pos_x,ben.head->pos_y);
		ben.special.print_bul_old(ben.special.pos_x,ben.special.pos_y);
		Game::clear();
	}
	if(room.time_count>=room.time_max) 
	{	
		Vector tem; double tem1;
		square.paint_room_new(square.pos_x,square.pos_y,square.pos,square.angle);
		room.new_door(room.door,square.angle,1);
		ben.cur=ben.cur>1?ben.cur:ben.cur+2;
		if(judge_coll_single(ben.print_chara,7,room.door,5,tem,tem1)==true   )
		{
			memset(room.monster,0,sizeof(room.monster));
			Monster::num_total=0;
			Monster::num_count=0;
			Game::clear();
			room.new_room(room_count);
			if(  ben.num_count[2]>2  )
				room_count+=0;
			else
				room_count++;
			ben.num_count[2]=0;
			judge_update=0;
			ben.print_cha_old(ben.pos_x,ben.pos_y,ben.print_chara);
			ben.pos_x=2*square.pos_x-ben.pos_x;
			ben.pos_y=2*square.pos_y-ben.pos_y;
			ben.print_cha_new(ben.pos_x,ben.pos_y,ben.print_chara);
			room.time_count=0;
			ben.cur-=2;

		//	if(ben.ski[ben.cur]==1)
			{
				if(ben.last!=ben.head)
				{
					Bullet *bul=ben.head->nex,*pre_bul=ben.head;
					ben.head->print_bul_old(ben.head->pos_x,ben.head->pos_y);
					ben.head->exist=false;
					while(bul!=NULL)
					{
						bul->exist=false;
						{
							bul->print_bul_old(bul->pos_x,bul->pos_y);
							if(bul->nex!=NULL)
							{	
								pre_bul->nex=bul->nex;
								if(bul!=NULL)
									delete bul;
								bul=pre_bul->nex;
								continue;
							}
						}
						pre_bul=pre_bul->nex;
						bul=bul->nex;
					}
				}
				if(ben.head->nex==NULL)
				{	
					ben.head->nex=ben.last;
					ben.last->nex=NULL;
				}
			}
		}
	}
}
void Game::bomb_hurt(int mod)
{
	if(mod==1)
	{
		setlinestyle(PS_SOLID, 1); setlinecolor(RGB( 255 , 255 , 0 ));
		setfillcolor(RGB( 255 , 255 , 0 ));
		ben.num_count[ben.ski[ben.cur]]=0;
		Vector circle_up(ben.head->pos_x-75,ben.head->pos_y-75),circle_down(ben.head->pos_x+75,ben.head->pos_y+75);
		for(int i=0; i<400; i++)
		{
			if(room.monster[i].exist==false) continue;
			if( (room.monster[i].pos_x-ben.head->pos_x)*(room.monster[i].pos_x-ben.head->pos_x)+(room.monster[i].pos_y-ben.head->pos_y)*(room.monster[i].pos_y-ben.head->pos_y)<=75*75  )
			{	
				room.monster[i].print_old(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
				room.monster[i].exist=false;
				if(room.monster[i].special==0)
					death_count++;
				else
					death_count+=3;
				Monster::num_total--;
				continue;
			}
			if( judge_circle_coll(circle_up,circle_down,room.monster[i].pos,room.monster[i].num_edge)==true  )
			{
				room.monster[i].print_old(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
				room.monster[i].exist=false;
				if(room.monster[i].special==0)
					death_count++;
				else
					death_count+=3;
				Monster::num_total--;
			}
		}
		if( ( (ben.pos_x-ben.head->pos_x)*(ben.pos_x-ben.head->pos_x)+(ben.pos_y-ben.head->pos_y)*(ben.pos_y-ben.head->pos_y)<=75*75) || ( judge_circle_coll(circle_up,circle_down,ben.print_chara,7)==true  )  )
			if(ben.judge_hurt==-1)
			{
				ben.judge_hurt++;
				ben.life_now--;
			}
		setlinestyle(PS_SOLID, 1); setlinecolor(RGB( 255 , 255 , 0 ));
		setfillcolor(RGB( 255 , 255 , 0 ));
		fillellipse( ben.head->pos_x-75, ben.head->pos_y-75, ben.head->pos_x+75, ben.head->pos_y+75);
	}
	else
	{
		setlinestyle(PS_SOLID, 1); setlinecolor(RGB( 0 , 0 , 255 ));
		setfillcolor(RGB( 0 , 0 , 255 ));
		ben.num_count[ben.ski[ben.cur]]=0;
		Vector circle_up(ben.last_special.pos_x-90,ben.last_special.pos_y-90),circle_down(ben.last_special.pos_x+90,ben.last_special.pos_y+90);
		for(int i=0; i<400; i++)
		{
			if(room.monster[i].exist==false) continue;
			if( (room.monster[i].pos_x-ben.last_special.pos_x)*(room.monster[i].pos_x-ben.last_special.pos_x)+(room.monster[i].pos_y-ben.last_special.pos_y)*(room.monster[i].pos_y-ben.last_special.pos_y)<=90*90  )
			{	
				room.monster[i].print_old(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
				room.monster[i].exist=false;
				if(room.monster[i].special==0)
					death_count++;
				else
					death_count+=3;
				Monster::num_total--;
				continue;
			}
			if( judge_circle_coll(circle_up,circle_down,room.monster[i].pos,room.monster[i].num_edge)==true  )
			{
				room.monster[i].print_old(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
				room.monster[i].exist=false;
				if(room.monster[i].special==0)
					death_count++;
				else
					death_count+=3;
				Monster::num_total--;
			}
		}
		setlinestyle(PS_SOLID, 1); setlinecolor(RGB( 0 , 0 , 255 ));
		setfillcolor(RGB( 0 , 0 , 255 ));
		fillellipse( ben.last_special.pos_x-90, ben.last_special.pos_y-90, ben.last_special.pos_x+90, ben.last_special.pos_y+90);
	}
}

//////////// Room ////////////////
Room::Room()
{
	new_room(0);
}
Room::~Room(){}
void Room::new_door(POINT door[], double angle, int mod)
{
	int squ_x=900,squ_y=495;
	double r1=sqrt(375*375*2),r2=sqrt(350*350*2);
	double x1=(sin(pi/4.0)/sin(5.0/8.0*pi))*r1-10 , x2=(sin(pi/4.0)/sin(5.0/8.0*pi))*r2-10;
	double rand_angle=pi/2*rand_c;
	POINT door11[]=
	{
		squ_x+x1*cos(3.0/8.0*pi+rand_angle+pi/110.0+angle), squ_y-x1*sin(3.0/8.0*pi+rand_angle+angle),
		squ_x+x1*cos(3.0/8.0*pi-pi/110.0+rand_angle+pi/4.0+angle), squ_y-x1*sin(3.0/8.0*pi+rand_angle+pi/4.0+angle)-1,
		squ_x+x2*cos(3.0/8.0*pi+rand_angle+pi/4.0+angle), squ_y-x2*sin(3.0/8.0*pi+rand_angle+pi/4.0+angle),
		squ_x+x2*cos(3.0/8.0*pi+rand_angle+angle), squ_y-x2*sin(3.0/8.0*pi+rand_angle+angle),
		squ_x+x1*cos(3.0/8.0*pi+rand_angle+pi/110.0+angle), squ_y-x1*sin(3.0/8.0*pi+rand_angle+angle)
	};
	for(int i=0; i<5; i++)
	{
		door[i].x=door11[i].x;
		door[i].y=door11[i].y;
	}
	if(mod==1)
	{
		setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 255 , 0 , 0 ));
		setfillcolor(RGB( 255 , 0 , 0 ));
	}
	else
	{
		setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 0 , 0 , 0 ));
		setfillcolor(RGB( 0 , 0 , 0 ));
	}
	fillpolygon(door , 5);
}
void Room::new_room(int a)
{
	num_stab=rand()%3+2;
	num_stone=rand()%4+2;
	time_count=0;
	rand_c=rand()%4;
	time_max=200+a*20+(rand()%2-1)*40;
	for(int j=0; j<rand()%3+1; j++)
	for(int i=0; i<num_stab; i++)
	{	
		stab[i].reset();
	//	stab[i].new_point();
	}
	for(int j=0; j<rand()%3+1; j++)
	for(int i=0; i<num_stone; i++)
	{	
		stone[i].reset();
		//stone[i].new_point();
	}
	for(int i=0; i<num_stab; i++)
	{
		for(int j=0; j<num_stab; j++)
		{
			if(i==j) continue;
			if( ((stab[i].pos_x-stab[j].pos_x)*(stab[i].pos_x-stab[j].pos_x)+(stab[i].pos_y-stab[j].pos_y)*(stab[i].pos_y-stab[j].pos_y))  <=3200  )
			{
				stab[i].reset();
				if(a!=0)
					stab[i].new_point();
			}
		}
		for(int j=0; j<num_stone; j++)
			if( ((stab[i].pos_x-stone[j].pos_x)*(stab[i].pos_x-stone[j].pos_x)+(stab[i].pos_y-stone[j].pos_y)*(stab[i].pos_y-stone[j].pos_y))  <=3200  )
				stone[j].reset();
	}
	for(int i=0 ; i<num_stone; i++)
	{
		for(int j=0; j<num_stone; j++)
		{
			if(i==j) continue;
			if( ((stone[i].pos_x-stone[j].pos_x)*(stone[i].pos_x-stone[j].pos_x)+(stone[i].pos_y-stone[j].pos_y)*(stone[i].pos_y-stone[j].pos_y))  <=3200  )
				stone[i].reset();
		}
	}
	Bullet::num_time_count=0;
	Monster::num_count=0;
	Monster::num_total=0;
	Game::num_monster_fresh=0;
	
}
void Room::update_monster(int x, int y, Square square)
{
	Game::num_monster_fresh++;
	double cc;
	if(Game::room_count<=15)
		cc=4*sin(Game::room_count*1.0)-1*Game::room_count*1.0+17-2*cos(2*Game::room_count*1.0);
	else 
		cc=1*sin(Game::room_count*1.0)+3-2*cos(2*Game::room_count*1.0);
	if(Game::num_monster_fresh>  cc   ) // 4*sin(x)-1*x+17-2*cos(2*x)    x<=15
		// 1*sin(x)+3-2*cos(2*x)
	{	
		Game::num_monster_fresh=0;
		monster[Monster::num_count++].create_new_monster(x,y,square);
		Monster::num_total++;
		if(Monster::num_count>400)
			Monster::num_count=0;
	}   //   a+b=20    5a+b=10   -2.5   22.5
	for(int i=0 ; i<400; i++)
		if(monster[i].exist==true)
		{
			get_path(monster[i].pos_x,monster[i].pos_y,x,y,monster[i].path,monster[i].special);
			monster[i].print_old(monster[i].pos_x,monster[i].pos_y,monster[i].num_edge,monster[i].pos);
			Vector tem(monster[i].path.x-monster[i].pos_x,monster[i].path.y-monster[i].pos_y);
			tem.new_normalize();
		/*	if((monster[i].path.y-monster[i].pos_y<2))
			{	tem.y=0;  tem.x=1;}
			if((monster[i].path.x-monster[i].pos_x)<2)
			{	tem.x=0;  tem.y=1;}
			if(( (monster[i].path.x-monster[i].pos_x)<2)&&( (monster[i].path.y-monster[i].pos_y<2)))
				tem.x=tem.y=0;  */
			monster[i].pos_x+= tem.x*monster[i].speed;
			monster[i].pos_y+= tem.y*monster[i].speed;
			monster[i].print_now(monster[i].pos_x,monster[i].pos_y,monster[i].num_edge,monster[i].pos);
			if(time_count>=time_max) 
				monster[i].speed+=0.02;
		}
	return;
}
void Room::get_path(int x ,int  y, int aim_x, int aim_y, POINT &path, int special)
{ 
/*	//  特判 若怪物到人路径上无障碍物， 则直线走
	{
		int i=0;
		for(; i<num_stab; i++)
		{
			if(special==1) break;
			if(abs(aim_x-x)<5)
			{
				if(  (stab[i].pos_x<= max(x,aim_x)+2*Obstacle::r) && (stab[i].pos_x>= min(x,aim_x)-2*Obstacle::r) && (stab[i].pos_y<=max(y,aim_y)+2*Obstacle::r)  && (stab[i].pos_y>=min(y,aim_y)-2*Obstacle::r) )
				break;//障碍物位于两者之间
			}
			if(abs(aim_y-y)<5)
			{if(stab[i].pos_y<= max(y,aim_y)+2*Obstacle::r &&stab[i].pos_y>= min(y,aim_y)-2*Obstacle::r && stab[i].pos_x<=max(x,aim_x)+2*Obstacle::r  &&stab[i].pos_x>=min(x,aim_x)-2*Obstacle::r )
				break;//障碍物位于两者之间
			}
			if( abs(aim_x-x)>3 )
			{
				double k=(aim_y-y)/(aim_x-x);
				double b=y-k*x;
				double dis=abs(k*stab[i].pos_x-stab[i].pos_y+b)/(k*k+1);
				double x1=( 1/k*stab[i].pos_x+stab[i].pos_y-b )/(k+1/k);
				double y1=k*x1+b;
				if(  (dis<=(3*Obstacle::r+0)) &&  (   ((  (x1>=min(aim_x,x)-2*Obstacle::r))  ) && ( x1<=max(aim_x,x)+2*Obstacle::r)) ) 
					break;  //障碍物位于两者之间
			}
		}
		int j=0;
		for(; j<num_stone; j++)
		{
			if(special==2) break;
			if(abs(aim_x-x)<5)
			{
				if(stone[j].pos_x<= max(x,aim_x)+2*Obstacle::r &&stone[j].pos_x>= min(x,aim_x)-2*Obstacle::r && stone[j].pos_y<=max(y,aim_y)+2*Obstacle::r  &&stone[j].pos_y>=min(y,aim_y)-2*Obstacle::r )
				break;//障碍物位于两者之间
			}
			if(abs(aim_y-y)<5)
			{
				if(stone[j].pos_y<= max(y,aim_y)+2*Obstacle::r &&stone[j].pos_y>= min(y,aim_y)-2*Obstacle::r && stone[j].pos_x<=max(x,aim_x)+2*Obstacle::r  &&stone[j].pos_x>=min(x,aim_x)-2*Obstacle::r )
				break;//障碍物位于两者之间
			}
			if( abs(aim_x-x)>3 )
			{
				double k=(aim_y-y)/(aim_x-x);
				double b=y-k*x;
				double dis=abs(k*stone[j].pos_x-stone[j].pos_y+b)/(k*k+1);
				double x1=( 1/k*stone[j].pos_x+stone[j].pos_y-b )/(k+1/k);
				double y1=k*x1+b;
				if(  (dis<=(3*Obstacle::r+0)) &&  (   ((  (x1>=min(aim_x,x)-2*Obstacle::r))  ) && ( x1<=max(aim_x,x)+2*Obstacle::r)) ) 
					break;  //障碍物位于两者之间
			}
		}
		if(i==num_stab&&j==num_stone) 
		{
			path.x=aim_x; 
			path.y=aim_y; 
			return; 
		}
	}*/
	//////////////////////////////////////////
	aim_x=get_i(normalize_x(aim_x)); aim_y=get_j(normalize_y(aim_y));
	int now_x= get_i(normalize_x(x)), now_y=get_j(normalize_y(y));
	int mon_x=get_i(normalize_x(x)),mon_y=get_j(normalize_y(y));
	int count=0;
	for(int i=0; i<42; i++)  // gx清空
		for(int j=0; j<42; j++)
			mapp[i][j].gx=0;
	//////////////////////////////////////
	POINT aim={ aim_x ,aim_y };
	POINT start_point={now_x , now_y};
	Node OPEN[10000],CLOSE[10000];
	POINT PATH[10000];
	Node empt;
	memset(OPEN,0,sizeof(OPEN));
	memset(CLOSE,0,sizeof(CLOSE));
	memset(PATH,0,sizeof(PATH));
	int first=0,last=0,last_close=0, end_path=0;
	OPEN[last++]=mapp[now_x][now_y];
	CLOSE[last_close]=mapp[now_x][now_y];
	///////
	bool findd=false;
while(findd==false)
{
	for(int i=first; i<last; i++)
		if( ((OPEN[i].ground>>1)&(1))==1)
		{
			OPEN[i].fa=CLOSE[last_close-1].pos;
			findd=true; break;
		}
		// 从OPEN表里找fx最小的并加入CLOSE表
	quicksort(first, last-1, OPEN);
	if(first<last)
		CLOSE[last_close++]=OPEN[first++];

		// 从新加入CLOSE表的点开始扩展
	now_x=CLOSE[last_close-1].pos.x;
	now_y=CLOSE[last_close-1].pos.y;
	for(int i=now_x-1; i<=now_x+1 ; i++ ) // 枚举 now的周围八个方格
	{for(int j=now_y-1; j<=now_y+1; j++ )
	{
		if( i<0 || i>42 || j<0 || j>42 ) continue;
		if(i==now_x && j==now_y) continue;
		int flag=0;
		for(int cc=first; cc<last; cc++) // 在OPEN列表里找
			if(OPEN[cc].pos.x==i && OPEN[cc].pos.y==j)
			{	flag=1; break; } // flag==1 表明找到了
		if(flag==1 && last_close>0)  // 在OPEN列表里找到
		{
			int tem_find_place=0;
			for(int cc=first; cc<last ; cc++)
				if( OPEN[cc].pos.x==i && OPEN[cc].pos.y==j  )
					tem_find_place=cc; // 在OPEN表里定位
			int tem_gx=0;
			if( i==now_x || j==now_y ) // 判断是否是斜对角
				tem_gx=CLOSE[last_close-1].gx+10;
			else
				tem_gx=CLOSE[last_close-1].gx+14;
			if(tem_gx<OPEN[tem_find_place].gx)
			{
				OPEN[tem_find_place].fa.x=i;
				OPEN[tem_find_place].fa.y=j;
				mapp[OPEN[tem_find_place].pos.x][OPEN[tem_find_place].pos.y].fa.x =i;
				mapp[OPEN[tem_find_place].pos.x][OPEN[tem_find_place].pos.y].fa.y =j;
			}
			continue;
		}
		for(int cc=0; cc<last_close ; cc++)
			if(CLOSE[cc].pos.x==i && CLOSE[cc].pos.y==j)
			{flag=1; break;}
		if(flag==1) continue;
		// 地图标识号判定
		if(special==0 || special==3)
			if( (mapp[i][j].ground&(1))!=0) 
				continue;
		if(special==1)
			if( ( (mapp[i][j].ground>>3)&(1))!=0  && ( ( (mapp[i][j].ground>>1 )&(1))==0) && ( (mapp[i][j].ground&(1))!=0) ) 
				continue;
		if(special==2)
			if( ( (mapp[i][j].ground>>4)&(1))!=0  && ( ( (mapp[i][j].ground>>1 )&(1))==0) && ( (mapp[i][j].ground&(1))!=0) )
				continue;
		mapp[i][j].fa=mapp[now_x][now_y].pos;
		if( i==now_x || j==now_y ) // 判断是否是斜对角
			mapp[i][j].gx+=10;
		else
			mapp[i][j].gx+=14;
		OPEN[last++]=mapp[i][j];
	}
	}
	count++;    // 异常状态弹出
	if(count>9600)
	{
		path.x=aim_x;
		path.y=aim_y;
		return;
	}
}
	count=0;
	///////////////////////////
	Node temp=mapp[aim_x][aim_y];
	while( temp.pos.x!=mapp[mon_x][mon_y].pos.x || temp.pos.y!=mapp[mon_x][mon_y].pos.y )
	{
		PATH[end_path++]=temp.pos;   // 记录路径
		temp=mapp[temp.fa.x][temp.fa.y];   // 回溯至父节点
		count++;
		if(count>6666)
		{path.x=aim_x;path.y=aim_y;return;}
	}
	POINT ans={ get_x_from_i(PATH[end_path-1].x) , get_y_from_j(PATH[end_path-1].y) };
	path=ans;
	return;
}
/*Room	 Room::operator = (const Room & a )
{
/*	this->num_stab=a.num_stab;
	this->num_stone=a.num_stone;
	this->rand_c=a.rand_c;
	this->time_max=a.time_max;
	for(int i=0; i<5; i++) this->door[i]=a.door[i];
	for(int i=0; i<500; i++) this->monster[i]=a.monster[i];
	
}*/

/////////// Charactor ////////////////
Charactor::Charactor() 
{
	set_new_data(1);
}
void Charactor::print_cha_new(double x,double y,POINT print_chara[])
{
	if(judge_hurt!=-1) // 受伤时闪烁
	{
		if(judge_hurt%4==0)
		{	print_cha_old(x,y,print_chara);
			return;
		}
	}
	print_cha_old(x,y,print_chara);
	if(mod==1)
	{
		new_point(x,y,print_chara);
		setlinestyle(PS_SOLID, 1); setlinecolor(RGB(123,123,123));
		setfillcolor(RGB(123,123,123));
		fillpolygon(print_chara ,7);
		if(ski[cur]!=2 && ski[cur]!=0)
		{	
			setlinestyle(PS_SOLID, 1); setlinecolor(RGB(217,31,37));
			setfillcolor(RGB(217,31,37));
			if(GetAsyncKeyState(VK_UP)<0) 
			{	fillellipse(x-10,y-25,x+10,y-5); return ; }
			else if(GetAsyncKeyState(VK_DOWN)<0) 
			{	fillellipse(x-10,y+5,x+10,y+25); return ; }
			else if(GetAsyncKeyState(VK_LEFT)<0)
			{	fillellipse(x-25,y-10,x-5,y+10); return ; }
			else if(GetAsyncKeyState(VK_RIGHT)<0) 
			{	fillellipse(x+5,y-10,x+25,y+10); return ; }
			fillellipse(x+10,y-10,x-10,y+10);
		}
		else
		{
			setlinestyle(PS_SOLID,5); setlinecolor(RGB( 255 , 0 , 0 )); setfillcolor(RGB(255,0,0));
			ellipse(x-15,y-15,x+15,y+15);
		}
	}
	else if(mod==2|| mod==3)
	{
		setlinestyle(PS_SOLID); setlinecolor(RGB(255,255,255));
		setfillcolor(RGB(255,255,255));
		print_part_cha_new(x,y,print_chara);
		if(mod==3&&num_bul==0&&ski[cur]!=6) 
			print_cha_ball(x,y,0);
	//	if( (mod==2&&ski[cur]==4) || mod==3 )
			print_cha_line(x,y);
		if(GetAsyncKeyState(VK_UP)<0) 
		{
			print_cha_old(x,y,print_chara);
			judge_dir=1;print_part_cha_new(x,y,print_chara);
			if(mod==2)
			{
				if(ski[cur]!=2 && ski[cur]!=0)
				{	
					if( ski[cur]!=4 )
					{
						setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 255 , 0 , 0 ));
					}
					else
					{
						setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 0 , 0 , 0 ));
					}
					::line( x-18 , y-10 , x-2 , y-25 );
					::line( x+18 , y-10 , x+2 , y-25 );
				}
				else
				{
					setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 255 , 0 , 0 ));
					ellipse(x-15,y-15,x+15,y+15); 
				}
			}
			if(mod==3) 
			{
				print_cha_line(x,y); 
			}
		}
		else if(GetAsyncKeyState(VK_DOWN)<0) 
		{	
			print_cha_old(x,y,print_chara);
			judge_dir=3;
			print_part_cha_new(x,y,print_chara);
			if(mod==2)
			{
				if(ski[cur]!=2 && ski[cur]!=0)
				{	
					if( ski[cur]!=4 )
					{
						setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 255 , 0 , 0 ));
					}
					else
					{
						setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 0 , 0 , 0 ));
					}
					::line( x-18 , y+10 , x-2 , y+25 );
					::line( x+18 , y+10 , x+2 , y+25 );
				}
				else
				{
					setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 255 , 0 , 0 ));
					ellipse( x-15 , y-15 , x+15 , y+15);
				}
			}
			if(mod==3) 
			{
				print_cha_line(x,y); 
			}
		}
		else if(GetAsyncKeyState(VK_LEFT)<0)
		{	
			setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 255 , 0 , 0 ));
			print_cha_old(x,y,print_chara);judge_dir=2;
			print_part_cha_new(x,y,print_chara);
			if(mod==2)
			{
				if(ski[cur]!=2 && ski[cur]!=0)
				{	
					if( ski[cur]!=4 )
					{
						setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 255 , 0 , 0 ));
					}
					else
					{
						setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 0 , 0 , 0 ));
					}
					::line( x-20 , y-5 , x-8 , y-20);
					::line( x-20 , y+5 , x-8 , y+20);
 				}
				else
				{
					setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 255 , 0 , 0 ));
					ellipse(x-15,y-15,x+15,y+15);
				}
			}
			if(mod==3) 
			{
				print_cha_line(x,y); 
			}
		}
		else if(GetAsyncKeyState(VK_RIGHT)<0) 
		{	
			setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 255 , 0 , 0 ));
			print_cha_old(x,y,print_chara);
			judge_dir=4;
			print_part_cha_new(x,y,print_chara);
			if(mod==2)
			{
				if(ski[cur]!=2 && ski[cur]!=0)
				{	
					if( ski[cur]!=4 )
					{
						setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 255 , 0 , 0 ));
					}
					else
					{
						setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 255 , 0 , 0 ));
					}
					::line(x+20,y-5,x+8,y-20);
					::line(x+20,y+5,x+8,y+20);
				}
				else
				{
					setlinestyle(PS_SOLID, 5); setlinecolor(RGB( 255 , 0 , 0 ));
					ellipse(x-15,y-15,x+15,y+15);
				}
			}
			if(mod==3) 
			{
				print_cha_line(x,y); 
			}
		}
	}
	setlinestyle(PS_SOLID); setlinecolor(RGB( 255 , 255 , 255 ));
	setfillcolor(RGB(255,255,255));
}
void Charactor::print_cha_old(double x,double y,POINT print_chara[])
{
	setlinestyle(PS_SOLID, 1); setlinecolor(RGB(0,0,0));
	setfillcolor(RGB(0,0,0));
	new_point(x,y,print_chara);	
	fillpolygon(print_chara ,7);
	if(mod==3|| mod==2)
	{
		int tem=judge_dir;
		judge_dir=1;
		new_point(x,y,print_chara);	 
		fillpolygon( print_chara ,7);
		judge_dir=2;
		new_point(x,y,print_chara);	 
		fillpolygon( print_chara ,7);
		judge_dir=tem;
	}
	print_cha_ball(x,y,1);
}
void Charactor::new_point(double x,double y, POINT print_chara[])
{
	if( (mod==2|| mod==3)&& (judge_dir==2||judge_dir==4))
	{
		POINT apt1[]={x-40,y,x-14,y-30,x+14,y-30,x+40,y,x+14,y+30,x-14,y+30,x-40,y};
		for(int i=0; i<7 ; i++)
		{
			print_chara[i].x=apt1[i].x;
			print_chara[i].y=apt1[i].y;
		}
		return;
	}
	POINT apt1[]={x,y-40,x-30,y-14,x-30,y+14,x,y+40,x+30,y+14,x+30,y-14,x,y-40};
	for(int i=0; i<7 ; i++)
	{
		print_chara[i].x=apt1[i].x;
		print_chara[i].y=apt1[i].y;
	}
	return;
}
void Charactor::updateWithInput(double x,double y,POINT print_chara[])
{
	if(   ( ski[cur]==2 ) || ( ski[cur]==0 )  ) 
	{ 
		print_cha_new(pos_x,pos_y,print_chara);	 
		return; 
	}
	// 限制子弹、爆弹、激光射击频率
	if( (Bullet::num_time_count<3 &&  ( ski[cur]==1 ))  ||  (Bullet::num_time_count<10 &&  ( ski[cur]==3  )) || (Bullet::num_time_count<6 &&  ( ski[cur]==5 )) ||  (Bullet::num_time_count<10 &&  ( ski[cur]==4  )) ) 
		return;   
	Bullet::num_time_count=0;
	if((GetAsyncKeyState(VK_UP)<0)||(GetAsyncKeyState(VK_DOWN)<0)||(GetAsyncKeyState(VK_LEFT)<0)||(GetAsyncKeyState(VK_RIGHT)<0))
	{	
		if(mod==1)
		{
			print_part_cha_new(x,y,print_chara);
			setlinestyle(PS_SOLID, 1); setlinecolor(RGB(217,31,37));
			setfillcolor(RGB(217,31,37));
			if(GetAsyncKeyState(VK_UP)<0) 
				fillellipse(x-10,y-25,x+10,y-5);
			else if(GetAsyncKeyState(VK_DOWN)<0) 
				fillellipse(x-10,y+5,x+10,y+25);
			else if(GetAsyncKeyState(VK_LEFT)<0) 
				fillellipse(x-25,y-10,x-5,y+10); 
			else if(GetAsyncKeyState(VK_RIGHT)<0) 
				fillellipse(x+5,y-10,x+25,y+10);
		}
		if(ski[cur]==1)
		{
			num_bul++;
			if(GetAsyncKeyState(VK_UP)<0) 
			{	
				last->nex=new Bullet(pos_x,pos_y-25,pi/2);
				last=last->nex;
				last->cur=ski[cur];
			}
			else if(GetAsyncKeyState(VK_DOWN)<0) 
			{	
				last->nex=new Bullet(pos_x,pos_y+25,pi*3/2);
				last=last->nex;
				last->cur=ski[cur];
			}
			else if(GetAsyncKeyState(VK_LEFT)<0) 
			{	
				last->nex=new Bullet(pos_x-25,pos_y,pi);
				last=last->nex;
				last->cur=ski[cur];
			}
			else if(GetAsyncKeyState(VK_RIGHT)<0) 
			{	
				last->nex=new Bullet(pos_x+25,pos_y,0);
				last=last->nex;
				last->cur=ski[cur];
			}
		}
		if( ski[cur]==3 || ski[cur]==4)
		{
			last_line.life=line.life=Bullet::range[ski[cur]];
			last_line.cur=line.cur=ski[cur];
			last_line.exist=line.exist=true;
			last_line.pos_x=line.pos_x=pos_x;
			last_line.pos_y=line.pos_y=pos_y;
			if(GetAsyncKeyState(VK_UP)<0) 
			{	
				last_line.xita=line.xita=pi/2.0;
			}
			else if(GetAsyncKeyState(VK_DOWN)<0) 
			{	
				last_line.xita=line.xita=pi*3.0/2.0;
			}
			else if(GetAsyncKeyState(VK_LEFT)<0) 
			{	
				last_line.xita=line.xita=pi;
			}
			else if(GetAsyncKeyState(VK_RIGHT)<0) 
			{	
				last_line.xita=line.xita=0.0;
			}
		}
		if(ski[cur]==5)
		{	
				
			if(num_bul!=0 || (num_count[ski[cur]]<=1 &&num_count[ski[cur]]!=-1 )) return;
			num_bul=1;
			if(GetAsyncKeyState(VK_UP)<0) 
				head=new Bullet(pos_x,pos_y-25,pi/2);
			if(GetAsyncKeyState(VK_DOWN)<0) 
				head=new Bullet(pos_x,pos_y+25,pi*3/2);
			if(GetAsyncKeyState(VK_LEFT)<0) 
				head=new Bullet(pos_x-25,pos_y,pi+0.1);
			if(GetAsyncKeyState(VK_RIGHT)<0) 
				head=new Bullet(pos_x+25,pos_y,0);
			head->cur=ski[cur];
		}
		if(ski[cur]==6)
		{
			special.print_bul_old(special.pos_x,special.pos_y);
			if(GetAsyncKeyState(VK_UP)<0) 
				special.pos_y-=special.speed[special.cur]/2;
			if(GetAsyncKeyState(VK_DOWN)<0) 
				special.pos_y+=special.speed[special.cur]/2;
			if(GetAsyncKeyState(VK_LEFT)<0) 
				special.pos_x-=special.speed[special.cur]/2;
			if(GetAsyncKeyState(VK_RIGHT)<0) 
				special.pos_x+=special.speed[special.cur]/2;
			special.print_bul_new(special.pos_x,special.pos_y);
			special.cur=ski[cur];
		}
	}
	else
	{
		print_cha_new(pos_x,pos_y,print_chara);	
	}
	return ;
}
void Charactor::print_part_cha_new(double x,double y, POINT print_chara[])
{
	new_point(x,y,print_chara);
	if(mod==1)
	{
		setlinestyle(PS_SOLID, 1); setlinecolor(RGB(123,123,123));
		setfillcolor(RGB(123,123,123));
	}
	if(mod==2)
	{
		setlinestyle(PS_SOLID, 1); setlinecolor(RGB(199,97,20));
		setfillcolor(RGB(3,168,158));
	}
	if(mod==3)
	{
		setlinestyle(PS_SOLID, 1); setlinecolor(RGB(255,99,71));
		setfillcolor(RGB(218,112,214));
	}
	fillpolygon(print_chara ,7);
	if(mod==3)
	{
		if(ski[cur]!=6 && ski[cur]!=0 && ski[cur]!=2)
		{
			setlinestyle(PS_SOLID, 5); setlinecolor(RGB(255,0,0));
		}
		else
		{
			setlinestyle(PS_SOLID, 5); setlinecolor(RGB(0,0,0));
		}
		if(judge_dir==1 ||judge_dir==3)
		{
			::line(x-20,y-12,x-20,y+12);
			::line(x+20,y-12,x+20,y+12);
		}
		else
		{
			::line(x-12,y-20,x+12,y-20);
			::line(x-12,y+20,x+12,y+20);
		}
	}
	return;
}
void Charactor::print_cha_line(double x, double y)
{
	if(ski[cur]==5 || ski[cur]==3 || ski[cur]==1)
	{
		setlinestyle(PS_SOLID, 5); setlinecolor(RGB(255,0,0));
	}
	else
	{
		setlinestyle(PS_SOLID, 5); setlinecolor(RGB(0,0,0));
	}
	if(judge_dir==1 || judge_dir==3)
	{   
		::line(x-20,y-12,x-20,y+12);
		::line(x+20,y-12,x+20,y+12);
	}
	else
	{   
		::line(x-12,y-20,x+12,y-20);
		::line(x-12,y+20,x+12,y+20);
	}
}
void Charactor::print_cha_ball(double x, double y,bool judge_old)
{
	if(mod!=3) return;
	setlinestyle(PS_SOLID, 1); setlinecolor(RGB(255,255,255));
	setfillcolor(RGB(255,255,255));
	if(judge_old==0)
		setfillcolor(RGB(8,46,84));
	else
	{
		setlinestyle(PS_SOLID, 1); setlinecolor(RGB(0,0,0));
		setfillcolor(RGB(0,0,0));
	}
	if(judge_dir==1)
		fillellipse(x-10,y-45,x+10,y-25);
	if(judge_dir==2)
		fillellipse(x-45,y-10,x-25,y+10);
	if(judge_dir==3)
		fillellipse(x-10,y+45,x+10,y+25);
	if(judge_dir==4)
		fillellipse(x+45,y-10,x+25,y+10);
}
void Charactor::set_new_data(int md)
{
	pos_x=1100; 
	pos_y=680;
	judge_hurt=-1;
	judge_dir=1;
	ski[1]=ski[2]=ski[3]=ski[4]=0;
	cur=0;
	new_point(pos_x,pos_y,print_chara);
	memset(num_count,0,sizeof(num_count));
	num_count[3]=-1;
	num_bul=0;
	life_now=life=10;
	speed=10;
	special.r=30;
	head=new Bullet;
	head->exist=false;
	head->nex=NULL;
	last=head;

	special.pos_x=pos_x;
	special.pos_y=pos_y;
	if(md==1)
	{
		mod=1;
	}
	if(md==2)
	{
		mod=2;
		speed=14;
	}
	if(md==3)
	{
		mod=3;
		life_now=life=12;
	}
}
void Charactor::update()
{
	if(judge_hurt!=-1)
	{
		judge_hurt++;
		if(judge_hurt>20)
			judge_hurt=-1;
	}

	if(ski[cur]==5 || ski[cur]==6)
	{
		if(num_count[ski[cur]]==-1) return;
		num_count[ski[cur]]++;
		if(num_count[ski[cur]]>1)
		{
			num_count[ski[cur]]=-1;
			setlinestyle(PS_SOLID, 1); setlinecolor(RGB(0,0,0));
			setfillcolor(RGB(0,0,0));
			if(ski[cur]==5)
			{	// 抹除爆弹的爆炸痕迹
				fillellipse(head->pos_x-75, head->pos_y-75, head->pos_x+75,head->pos_y+75);
			}
			else   // 抹除食弹的爆炸痕迹
				fillellipse( last_special.pos_x-90, last_special.pos_y-90, last_special.pos_x+90, last_special.pos_y+90);
		}
	}
	return;
}

/////////// Square ////////////////
void Square::new_room_point(double squ_x, double squ_y, double angle , POINT pos[])
{
	double init=3.1415926/4.0,r1=sqrt(375*375*2),r2=sqrt(350*350*2);
	double tot=0.0822469;
	POINT squ1[]=
	{
		squ_x+r1*cos(init*3.0+angle),     squ_y-r1*sin(3.0*init+angle),		//左上远
		squ_x+r1*cos(init*5.0+angle),     squ_y-r1*sin(init*5.0+angle),		//左下远
		squ_x+r1*cos(-init+angle),     squ_y-r1*sin(-init+angle),		//右下远
		squ_x+r1*cos(init+angle),     squ_y-r1*sin(init+angle),		//右上远
		squ_x+r1*cos(init*3.0+angle),     squ_y-r1*sin(3.0*init+angle),  	//左上远

		squ_x+r2*cos(init*3.0+angle),     squ_y-r2*sin(3.0*init+angle),		//左上近
		squ_x+r2*cos(init*5.0+angle),     squ_y-r2*sin(init*5.0+angle),		//左下近
		squ_x+r2*cos(-init+angle),     squ_y-r2*sin(-init+angle),		//右下近
		squ_x+r2*cos(init+angle),     squ_y-r2*sin(init+angle),		//右上近
		squ_x+r2*cos(init*3.0+angle),     squ_y-r2*sin(3.0*init+angle),  	//左上近
	};
	POINT tem_corner[]=
	{
		squ_x+r2*cos(init*3.0+angle),     squ_y-r2*sin(3.0*init+angle),	  //左上近
		squ_x+r2*cos(init*5.0+angle),     squ_y-r2*sin(init*5.0+angle),	  //左下近
		squ_x+r2*cos(-init+angle),     squ_y-r2*sin(-init+angle),	  //右下近
		squ_x+r2*cos(init+angle),     squ_y-r2*sin(init+angle)    //右上近
	};
	POINT  tedge1[]=
	{
		squ_x+r2*cos(init*3.0+angle),     squ_y-r2*sin(3.0*init+angle), //左上近
		squ_x+r2*cos(init*5.0+angle),     squ_y-r2*sin(init*5.0+angle),  //左下近
		squ_x+r1*cos(init*5.0+angle),     squ_y-r1*sin(init*5.0+angle),
		squ_x+r1*cos(init*3.0+angle),     squ_y-r1*sin(3.0*init+angle),
		squ_x+r2*cos(init*3.0+angle),     squ_y-r2*sin(3.0*init+angle)
	};
	POINT tedge2[]=
	{
		squ_x+r2*cos(-init+angle),     squ_y-r2*sin(-init+angle), //右下近
		squ_x+r2*cos(init+angle),     squ_y-r2*sin(init+angle),  //右上近
		squ_x+r1*cos(init+angle),     squ_y-r1*sin(init+angle),
		squ_x+r1*cos(-init+angle),     squ_y-r1*sin(-init+angle),
		squ_x+r2*cos(-init+angle),     squ_y-r2*sin(-init+angle)
	};
	POINT tedge3[]=
	{
		squ_x+r2*cos(init*5.0+angle),     squ_y-r2*sin(init*5.0+angle),		//左下近
		squ_x+r2*cos(-init+angle),     squ_y-r2*sin(-init+angle), //右下近
		squ_x+r1*cos(-init+angle),     squ_y-r1*sin(-init+angle),
		squ_x+r1*cos(init*5.0+angle),     squ_y-r1*sin(init*5.0+angle),		//左下远
		squ_x+r2*cos(init*5.0+angle),     squ_y-r2*sin(init*5.0+angle)
	};
	POINT tedge4[]=
	{
		squ_x+r2*cos(init+angle),     squ_y-r2*sin(init+angle),		//右上近
		squ_x+r2*cos(init*3.0+angle),     squ_y-r2*sin(3.0*init+angle), //左上近
		squ_x+r1*cos(init*3.0+angle),     squ_y-r1*sin(3.0*init+angle),
		squ_x+r1*cos(init+angle),     squ_y-r1*sin(init+angle),		//右上远
		squ_x+r2*cos(init+angle),     squ_y-r2*sin(init+angle)
	};

	for(int i=0; i<10 ; i++)
	{pos[i].x=squ1[i].x;pos[i].y=squ1[i].y;}
	for(int i=0; i<5; i++)
	{edge1[i].x=tedge1[i].x;edge1[i].y=tedge1[i].y;}
	for(int i=0; i<5; i++)
	{edge2[i].x=tedge2[i].x;edge2[i].y=tedge2[i].y;}
	for(int i=0; i<5; i++)
	{edge3[i].x=tedge3[i].x;edge3[i].y=tedge3[i].y;}
	for(int i=0; i<5; i++)
	{edge4[i].x=tedge4[i].x;edge4[i].y=tedge4[i].y;}
	for(int i=0; i<4; i++)
	{corner[i].x=tem_corner[i].x; corner[i].y=tem_corner[i].y;}
	return;
}
void Square::paint_room_new(double squ_x, double squ_y, POINT squ[], double angle)
{
	setlinestyle(PS_SOLID, 1); setlinecolor(RGB(255,255,255));
	setfillcolor(RGB(255,255,255));
	double init=3.1415926/4.0,r1=sqrt(375*375*2),r2=sqrt(350*350*2);
	new_room_point(squ_x,squ_y,angle,squ);
	fillpolygon(squ ,10);
}
void Square::paint_room_old(double squ_x, double squ_y, POINT squ[],double angle)
{
	setlinestyle(PS_SOLID, 1); setlinecolor(RGB(0,0,0));
	setfillcolor(RGB(0,0,0));
	double init=3.1415926/4.0,r1=sqrt(375*375*2),r2=sqrt(350*350*2);
	new_room_point(squ_x,squ_y,angle,squ);
	fillpolygon(squ ,10);
}
Square::Square()
{
	pos_x=900; 
	pos_y=495;
	angle=0.0;
	init=pi/4.0;
	speed=8;
	jud_way=0;
	new_room_point(pos_x,pos_y,angle,pos);
}
void Square::judge_input( int ski)
{
	if(  ski==0 || ski==2 )
	if((GetAsyncKeyState(VK_LEFT)<0)||(GetAsyncKeyState(VK_RIGHT)<0))
	{
		if(ski==0)
			cyclooctane.room.new_door(cyclooctane.room.door,angle,0);
		paint_room_old(pos_x,pos_y,pos,angle);
		if(GetAsyncKeyState(VK_LEFT)<0) { angle+=speed/100; jud_way=1; }
		if(GetAsyncKeyState(VK_RIGHT)<0) { angle-=speed/100; jud_way=2; }
		paint_room_new(pos_x,pos_y,pos,angle);
		if(ski==0)
			cyclooctane.room.new_door(cyclooctane.room.door,angle,1);
	}
	return;
}

/////////// Bullet ////////////////
Bullet::Bullet(double x,double y,double xi)
{
	pos_x=x; pos_y=y;
	xita=xi;
	nex=NULL;
	exist=true;
	life=0;
	r=5;
	cur=0;
	special=false;
}
Bullet::Bullet()
{
	pos_x=pos_y=0;
	exist=false;
	r=5;
	special=false;
	nex=NULL;
	xita=0;
	life=0;
	cur=0;
}
void Bullet::print_bul_new(double pos_x, double pos_y)
{
	setlinestyle(PS_SOLID, 1); setlinecolor(RGB(100,210,140));
	setfillcolor(RGB(100,210,140));
	fillellipse( pos_x-r, pos_y-r, pos_x+r, pos_y+r);
}
void Bullet::print_bul_old(double pos_x, double pos_y)
{
	setlinestyle(PS_SOLID, 1); setlinecolor(RGB(0,0,0));
	setfillcolor(RGB(0,0,0));
	fillellipse(  pos_x-r, pos_y-r, pos_x+r, pos_y+r);
}
void Bullet::operator =(Bullet a)
{
	this->pos_x=a.pos_x,
	this->pos_y=a.pos_y;
	this->xita=a.xita;
	this->exist=a.exist;
	this->life=a.life;
	this->special=a.special;
	return;
}

/////////// Monster ////////////////
Monster::Monster(int num)
{
	exist=false;
}
Monster::Monster()
{
/*	pos_x=1000;
	pos_y=600;
	speed=10;
	srand(time(0));
	num_edge=rand()%4+3;
	exist=true;
	new_point(pos_x,pos_y,num_edge,pos);*/
	exist=false;
}
void Monster::new_point(int x, int y, int num_edge, POINT pos[])
{
	if(num_edge==3)
	{
		POINT temp[]={x+20, y-20, x-20 , y-20, x, y+20 ,x+20, y-20 };
		for(int i=0; i<num_edge+1; i++)
		{
			pos[i].x=temp[i].x;
			pos[i].y=temp[i].y;
		}
	}
	if(num_edge==4)
	{
		POINT temp[]={x-20,y-20, x+20,y-20, x+20,y+20, x-20,y+20, x-20,y-20};
		//POINT temp[]={x-100,y-100,x+100,y-100,x-100,y+100,x+100,y+100,x-100,y-100};
		for(int i=0; i<num_edge+1; i++)
		{
			pos[i].x=temp[i].x;
			pos[i].y=temp[i].y;
		}
	}
	if(num_edge==5)
	{
		POINT temp[]={x,y-25,  x-25,y-3 ,x-15,y+25,x+15,y+25 ,  x+25,y-3  ,x,y-25};
		//POINT temp[]={x-100,y-100,x+100,y-100,x-100,y+100,x+100,y+100,x-100,y-100};
		for(int i=0; i<num_edge+1; i++)
		{
			pos[i].x=temp[i].x;
			pos[i].y=temp[i].y;
		}
	}
	if(num_edge==6)
	{
		POINT temp[]={x,y-30,x-25,y-15,x-25,y+15,x,y+30,x+25,y+15,x+25,y-15,x,y-30};
		//POINT temp[]={x-100,y-100,x+100,y-100,x-100,y+100,x+100,y+100,x-100,y-100};
		for(int i=0; i<num_edge+1; i++)
		{
			pos[i].x=temp[i].x;
			pos[i].y=temp[i].y;
		}
	}
}
void Monster::print_now(int x, int y, int num, POINT pos[])
{
	new_point(x,y,num,pos);
	setlinestyle(PS_SOLID, 1); 
	if(special==0)
	{
		if(num_edge==3)
		{
			setlinecolor(RGB(255,99,71));
			setfillcolor(RGB(64,224,205));
		}
		if(num_edge==4)
		{
			setlinecolor(RGB(255,0,202));
			setfillcolor(RGB(255,192,202));
		}
		if(num_edge==5)
		{
			setlinecolor(RGB(64,224,205));
			setfillcolor(RGB(210,180,140));
		}
		if(num_edge==6)
		{
			setlinecolor(RGB(0,255,0));
			setfillcolor(RGB(160,32,240));
		}
	}
	else if(special==1)
	{
		setlinecolor(RGB(227,23,13));
		setfillcolor(RGB(227,23,13));
	}
	else if(special==2)
	{
		setlinecolor(RGB(199,97,20));
		setfillcolor(RGB(199,97,20));
	}
	else
	{
		setlinecolor(RGB(255,255,255));
		setfillcolor(RGB(255,255,255));
	}
	fillpolygon( pos ,num+1);
}
void Monster::print_old(int x, int y, int num, POINT pos[])
{
	setlinestyle(PS_SOLID, 1); setlinecolor(RGB(0,0,0));
	setfillcolor(RGB(0,0,0));
	new_point(x,y,num,pos);
	fillpolygon(pos ,num+1);
}
void Monster::create_new_monster(int x,int y, Square square)
{
	exist=true;
	double cc=0.85 - exp(-0.2*Game::room_count*1.0)+0.06*sin(-2*Game::room_count*1.0)+0.06*cos(-2*Game::room_count*1.0);
	cc=abs(cc)*100;
	// special==1\2\3 speed==8          special==0,speed=5
	if(  Game::room_count==5 || Game::room_count==10 || Game::room_count==14  || (Game::room_count>15&&Game::room_count%5==0)   )
	{
		int rs=rand()%3+1;
		speed=8;
		special=rs;
	}
	else
	{
		int r_tem=rand()%100+1;
		if(r_tem>=cc)
		{
			special=0; speed=5;
		}
		else
		{
			int rs=rand()%3+1;
			speed=8;
			special=rs;
		}
	}
	int rand1=rand()%2==0?1:-1,rand2=rand()%2==0?1:-1;
	int flag=1;
	while( flag>0 )
	{
		flag=0;
		pos_x=rand1*rand()%300+900;   // 900 495
		pos_y=rand2*rand()%300+495;
		POINT tem={pos_x,pos_y};
		if(((pos_x-x)*(pos_x-x)+(pos_y-y)*(pos_y-y))<75*75) flag++;
		if( judge_p_left_right(tem,square.edge1[0],square.edge1[1])==false ) flag++;
		if( judge_p_left_right(tem,square.edge2[0],square.edge2[1])==false ) flag++;
		if( judge_p_left_right(tem,square.edge3[0],square.edge3[1])==false ) flag++;
		if( judge_p_left_right(tem,square.edge4[0],square.edge4[1])==false ) flag++;
	}
	num_edge=rand()%4+3;
	path.x=pos_x;
	path.y=pos_y;
	new_point(pos_x,pos_y,num_edge,pos);
}

/////////// Obstacle ////////////////
void Obstacle::print_old()
{
	setlinestyle(PS_SOLID, 1); setlinecolor(RGB(0,0,0));
	setfillcolor(RGB(0,0,0));
	fillrectangle(pos_x-r,pos_y-r,pos_x+r,pos_y+r );
}
void Obstacle::new_center(double angle1)
{
	init+=angle1;
	pos_x=900+dis*(cosf(init));
	pos_y=495-dis*(sinf(init));
	new_point();
}
Obstacle::Obstacle()
{
}

Stab::Stab()
{
	reset();
}
void Stab::print_now(double angle)
{
	print_old();
	new_center(angle);
	setlinestyle(PS_SOLID, 1); 
	setlinecolor(RGB(255,0,0));
	setfillcolor(RGB(255,0,0));
	fillrectangle(pos_x-r,pos_y-r,pos_x+r,pos_y+r );
	new_point();
}
Stab::Stab(double x, double y)
{
	pos_x=x; pos_y=y;
	count=rand()%5;
	new_point();
	Vector a(900-pos_x,495-pos_y);
	init=acosf( (a.x-1) / a.get_lenth());
}
void Stab::new_point()
{
	if(judge_show==false) return;
	int tot=0;
	for(int i=0 ;i<3; i++)
	{
		POINT tem_stab[]=
		{ 
			pos_x-r+5 , pos_y-r+tot+10,
			pos_x-r+10 , pos_y-r+tot+5,
			pos_x-r+15,pos_y-r+tot+10,
			pos_x-r+20,pos_y-r+tot+5,
			pos_x-r+25,pos_y-r+tot+10,
			pos_x-r+30,pos_y-r+tot+5,
			pos_x-r+35,pos_y-r+tot+10
		};
		for(int i=0; i<7; i++)
		{
			stab[i].x=tem_stab[i].x;
			stab[i].y=tem_stab[i].y;
		}
		tot+=13;
		setlinestyle(PS_SOLID, 5); 
		setlinecolor(RGB(0,0,0));
		polyline(stab,7);
		setlinestyle(PS_SOLID, 1); 
		setlinecolor(RGB(255,255,255));
		setfillcolor(RGB(255,255,255));
	}
	setlinestyle(PS_SOLID, 1); setlinecolor(RGB(255,255,255));
	setfillcolor(RGB(255,255,255));
	POINT edge1[]=
	{
		pos_x-r,pos_y-r,
		pos_x-r,pos_y+r,
		pos_x+r,pos_y+r,
		pos_x+r,pos_y-r,
		pos_x-r,pos_y-r
	};
	for(int i=0; i<5; i++)
	{
		pos[i].x=edge1[i].x;
		pos[i].y=edge1[i].y;
	}
	
}
void Stab::reset()
{
	judge_show=true;
	count=rand()%5;
	count_max=rand()%7+15;
	int c=rand()%3;
	if(c==2) count_max=MAX_INT;
	int rand1=rand()%2-1,rand2=rand()%2-1;
	pos_x=rand()%12+6;    // 900 495
	pos_y=rand()%12+6;
	pos_x=get_x_from_i(pos_x);
	pos_y=get_y_from_j(pos_y);
	Vector a(pos_x-900,495-pos_y);
	double tem=sqrt((pos_x-900)*((pos_x-900))+(pos_y-495)*(pos_y-495));
	if(abs(tem)<1e-6)  init=0;
	else
	{
		init=asinf((495-pos_y)/tem);
		if((pos_x-900)>1e-6)
		{
			if((495-pos_y)>1e-6) init=init;
			else init=init+pi2;
		}
		else
			init=pi-init;
	}
	dis=sqrt( (900-pos_x)*(900-pos_x) + (495-pos_y)*(495-pos_y) );
}
void Stab::fresh_point()
{
	int tot=0;
	for(int i=0 ;i<3; i++)
	{
		POINT tem_stab[]=
		{
			pos_x-r+5 , pos_y-r+tot+10,
			pos_x-r+10 , pos_y-r+tot+5,
			pos_x-r+15 , pos_y-r+tot+10,
			pos_x-r+20 , pos_y-r+tot+5,
			pos_x-r+25 , pos_y-r+tot+10,
			pos_x-r+30 , pos_y-r+tot+5,
			pos_x-r+35 , pos_y-r+tot+10
		};
		for(int i=0; i<7; i++)
		{
			stab[i].x=tem_stab[i].x;
			stab[i].y=tem_stab[i].y;
		}
		tot+=13;
	}
	POINT edge1[]=
	{
		pos_x-r , pos_y-r,
		pos_x-r , pos_y+r,
		pos_x+r , pos_y+r,
		pos_x+r , pos_y-r,
		pos_x-r , pos_y-r
	};
	for(int i=0; i<5; i++)
	{
		pos[i].x=edge1[i].x;pos[i].y=edge1[i].y;
	}
	Vector a(pos_x-900,495-pos_y);
	double tem=sqrt((pos_x-900)*((pos_x-900))+(pos_y-495)*(pos_y-495));
	if(abs(tem)<1e-6)  init=0;
	else
	{
		init=asinf((495-pos_y)/tem);
		if((pos_x-900)>1e-6)
		{
			if((495-pos_y)>1e-6) init=init;
			else init=init+pi2;
		}
		else
			init=pi-init;
	}
	dis=sqrt( (900-pos_x)*(900-pos_x) + (495-pos_y)*(495-pos_y) );
}

Stone::Stone()
{
	reset();
}
Stone::Stone(double x, double y)
{
	pos_x=x; pos_y=y;
	new_point();
	Vector a(900-pos_x,495-pos_y);
	init=acosf( (a.x-1) / a.get_lenth());
}
void Stone::new_point()
{
	POINT edge1[]=
	{
		pos_x-r,pos_y-r,pos_x-r,pos_y+r,pos_x+r,pos_y+r,pos_x+r,pos_y-r,pos_x-r,pos_y-r
	};
	for(int i=0; i<5; i++)
	{
		pos[i].x=edge1[i].x;pos[i].y=edge1[i].y;
	}
	
	return;
}
void Stone::print_now(double angle)
{
	print_old();
	new_center(angle);
	setlinestyle(PS_SOLID, 1); setlinecolor(RGB(199,97,20));
	setfillcolor(RGB(199,97,20));
	fillrectangle(pos_x-r,pos_y-r,pos_x+r,pos_y+r );
	new_point();
}
void Stone::reset()
{
	int rand1=rand()%2-1,rand2=rand()%2-1;
	pos_x=rand()%12+6;    // 900 495
	pos_y=rand()%12+6;
	pos_x=get_x_from_i(pos_x);
	pos_y=get_y_from_j(pos_y);
	new_point();
	Vector a(pos_x-900,495-pos_y);
	double tem=sqrt((pos_x-900)*((pos_x-900))+(pos_y-495)*(pos_y-495));
	if(abs(tem)<1e-6)  init=0;
	else
	{
		init=asinf((495-pos_y)/tem);
		if((pos_x-900)>1e-6)
		{
			if((495-pos_y)>1e-6) init=init;
			else init=init+pi2;
		}
		else
			init=pi-init;
	}
	dis=sqrt( (900-pos_x)*(900-pos_x) + (495-pos_y)*(495-pos_y) );
}
void Stone::fresh_point()
{
	//new_point();
	POINT edge1[]=
	{
		pos_x-r,pos_y-r,pos_x-r,pos_y+r,pos_x+r,pos_y+r,pos_x+r,pos_y-r,pos_x-r,pos_y-r
	};
	for(int i=0; i<5; i++)
	{
		pos[i].x=edge1[i].x;pos[i].y=edge1[i].y;
	}
	Vector a(pos_x-900,495-pos_y);
	double tem=sqrt((pos_x-900)*((pos_x-900))+(pos_y-495)*(pos_y-495));
	if(abs(tem)<1e-6)  init=0;
	else
	{
		init=asinf((495-pos_y)/tem);
		if((pos_x-900)>1e-6)
		{
			if((495-pos_y)>1e-6) init=init;
			else init=init+pi2;
		}
		else
			init=pi-init;
	}
	dis=sqrt( (900-pos_x)*(900-pos_x) + (495-pos_y)*(495-pos_y) );
}

/////////// Status ////////////////
State* MENU_START::transition(int x)  
{  
    switch(x)  
    {  
        case 2:  
            return &s2;  
		case 3:  
            return &s3;  
        case 6:  
            return &s6;  
		case 10:
			return &s10;
        default:  
            return &s1;  
    }  
}  
void MENU_START::eventt()
{
	settextstyle(80,40,_T("方正姚体"));  settextcolor(RGB(255,255,255));
	setlinestyle(PS_SOLID, 5); setlinecolor(RGB(255,0,0));
	LPCTSTR str_start=L"Start";
	LPCTSTR str_version=L"V2.0";
	LPCTSTR str_exit=L"Exit";
	LPCTSTR str_help=L"Help";
	LPCTSTR str_load=L"Load";
	LPCTSTR str_title=L"Cyclooctane";
	LPCTSTR str_sub_title=L"----Who's the Hunter Now?";
	int gamestatus=1;
	setlinestyle(PS_SOLID, 1); setlinecolor(RGB(123,123,123));
	setfillcolor(RGB(123,123,123));
	Game empt;
	empt.ben.mod=1;
	empt.ben.set_new_data(empt.ben.mod);
	empt.ben.print_cha_new(500,850,empt.ben.print_chara);
	getimage(&img_cha1, 500-40  , 850-40 ,80 ,80);
	empt.ben.mod=2;
	empt.ben.print_cha_new(750,850,empt.ben.print_chara);
	getimage(&img_cha2, 750-40  , 850-40 ,80 ,80);
	empt.ben.mod=3;
	empt.ben.print_cha_new(1000,850,empt.ben.print_chara);
	getimage(&img_cha3, 1000-40  , 850-45 ,80 ,85);

	POINT sqr_now[]={ 650,410, 855,410,  855,493,  650,493 ,  650,410 };
	while(1)	
	{
		BeginBatchDraw();
		putimage( 500-40  , 850-40 , &img_cha1);
		putimage( 750-40  , 850-40 , &img_cha2);
		putimage( 1000-40  , 850-45 , &img_cha3);
		setbkcolor(RGB(0,0,0));
		settextcolor(RGB(255,255,255));
		settextstyle(160,60,_T("微软雅黑"));  settextcolor(RGB(255,255,255));
		outtextxy(380,100,str_title);
		settextstyle(40,15,_T("微软雅黑"));  settextcolor(RGB(255,255,255));
		outtextxy(1130,195,str_version);
		settextstyle(40,15,_T("微软雅黑"));  settextcolor(RGB(255,255,255));
		outtextxy(850,280,str_sub_title);
		settextstyle(80,40,_T("Agency FB"));  settextcolor(RGB(255,255,255));
		outtextxy(655,410,str_start);
		outtextxy(660,510,str_load);
		outtextxy(665,610,str_help);
		outtextxy(680,710,str_exit);
		setlinestyle(PS_SOLID, 5); setlinecolor(RGB(255,0,0));
		polyline(sqr_now, 5);
		FlushBatchDraw();
		char aaa=_getch();
		if(aaa=='\r') break;
		if(aaa=='w'||aaa=='s')
		{
			if(aaa=='w')
				gamestatus=gamestatus>1?gamestatus-1:4;
			if(aaa=='s')
				gamestatus=gamestatus<4?gamestatus+1:1;
			Game::clear();
		}
		setlinestyle(PS_SOLID, 5); setlinecolor(RGB(255,0,0));
		if(gamestatus==1)
		{
			POINT sqr_a[]={ 650,410, 855,410,  855,493,  650,493 ,  650,410 };
			for(int i=0; i<5; i++) 
			{
				sqr_now[i].x=sqr_a[i].x;
				sqr_now[i].y=sqr_a[i].y;
			}
		}
		else if(gamestatus==2)
		{
			POINT sqr_a[]={ 655,510, 850,510, 850,593,  655,593 , 655,510 };
			for(int i=0; i<5; i++) 
			{
				sqr_now[i].x=sqr_a[i].x;
				sqr_now[i].y=sqr_a[i].y;
			}
		}
		else if(gamestatus==4)
		{
			POINT sqr_a[]={ 672,710, 820,710, 820,793, 672,793 , 672,710 }; 
			for(int i=0; i<5; i++) 
			{
				sqr_now[i].x=sqr_a[i].x;
				sqr_now[i].y=sqr_a[i].y;
			}
		}
		else if(gamestatus==3)
		{
			POINT sqr_a[]={ 655,610, 850,610, 850,693,  655,693 , 655,610 };
			for(int i=0; i<5; i++) 
			{
				sqr_now[i].x=sqr_a[i].x;
				sqr_now[i].y=sqr_a[i].y;
			}
		}
		polyline(sqr_now, 5);
		FlushBatchDraw();
	}
	EndBatchDraw();
	Game::clear();
	if(gamestatus==1)
	{	
		gamestatus=2;
		cyclooctane.fresh_data();

	}
	else if(gamestatus==2)
	{
		gamestatus=3;
		if(cyclooctane.read_data()!=true || cyclooctane.on_game==false)
			gamestatus=1;
	}
	else if(gamestatus==4)
		gamestatus=6;
	else
		gamestatus=10;
	FSM::current=transition(gamestatus);
	return;
}

State* MENU_CHA::transition(int x)  
{  
    switch(x)  
    {  
        case 1:  
            return &s1;  
        case 8:  
            return &s8;  
        default:  
            return &s2;  
    }  
}  
void MENU_CHA::eventt()
{
	/////////////////////////////////////
	cyclooctane.coin=999;
	////////////////////////////////////
	cyclooctane.read_data();
	settextstyle(80,40,_T("方正姚体"));  settextcolor(RGB(255,255,255));
	LPCTSTR str_ben=L"Benzene";
	LPCTSTR str_cyc=L"Cyclohexadiene";
	LPCTSTR str_pyran=L"Pyran";
	LPCTSTR str_title=L"Charactor";
	LPCTSTR str_lock2=L"解锁 ($20)";
	LPCTSTR str_lock3=L"解锁 ($20)";
	LPCTSTR str_cha3=L"life+2";
	LPCTSTR str_cha2=L"speed+4";
	int gamestatus=1;
	int tem_mod=1;
	BeginBatchDraw();
	setlinestyle(PS_SOLID, 1); setlinecolor(RGB(255,0,0));
	setfillcolor(RGB(255,0,0));
	fillellipse(310,690,325,700);
	setbkcolor(RGB(0,0,0));
	settextstyle(160,60,_T("微软雅黑"));  settextcolor(RGB(255,255,255));
	outtextxy(420,150,str_title);
	settextstyle(40,15,_T("微软雅黑"));  settextcolor(RGB(255,0,255));
	outtextxy(690,820,str_cha2);
	outtextxy(1140,820,str_cha3);
	if( cyclooctane.jud_skin2==false || cyclooctane.jud_skin3==false )
	{
		LOGFONT f;
		gettextstyle(&f); 
		_tcscpy(f.lfFaceName, _T("黑体"));   
		f.lfQuality = ANTIALIASED_QUALITY;  
		f.lfHeight = 35;  
		f.lfWidth=20;
		settextstyle(&f);   
		settextcolor(RGB(255,255,0));
		TCHAR s1[10]; 
		_stprintf(s1,_T("金币：%d"),cyclooctane.coin);
		outtextxy(80+100,350+20,s1);
		putimage(80,350,&img_coin1);
		if(cyclooctane.jud_skin2==false)
			outtextxy(650,750,str_lock2);
		if(cyclooctane.jud_skin3==false)
			outtextxy(1100,750,str_lock3);
	}
	settextstyle(80,40,_T("方正姚体"));  settextcolor(RGB(255,255,255));
	outtextxy(200,600,str_ben);
	outtextxy(550,600,str_cyc);
	outtextxy(1120,600,str_pyran);
	putimage(320-40  , 520-40 ,&img_cha1);
	putimage(770-40  , 520-40 ,&img_cha2);
	putimage(1200-40  , 520-45 ,&img_cha3);
	FlushBatchDraw();
	while(1)	
	{
		BeginBatchDraw();
		if(GetAsyncKeyState(VK_ESCAPE)<0)
		{	
			gamestatus=1;
			break;
		}
		if(_kbhit())
		{
			char aaa=_getch();
			if(aaa=='\r') 
			{	
				if(tem_mod==1 || (tem_mod==2&&cyclooctane.jud_skin2==true) || (tem_mod==3&&cyclooctane.jud_skin3==true))
				{
					gamestatus=8;
					break;
				}
				if(cyclooctane.coin<20)
				{
					tem_mod=1; 
				}
				else if(tem_mod==2)
				{
					cyclooctane.jud_skin2=true;
					cyclooctane.coin-=20;
					cyclooctane.write_data();
					putimage(300,370,&img_empt);
					putimage(650,750,&img_empt);
					LOGFONT f;
					gettextstyle(&f); 
					_tcscpy(f.lfFaceName, _T("黑体"));   
					f.lfQuality = ANTIALIASED_QUALITY;  
					f.lfHeight = 35;  
					f.lfWidth=20;
					settextstyle(&f);   
					settextcolor(RGB(255,255,0));
					TCHAR s1[10]; 
					_stprintf(s1,_T("金币：%d"),cyclooctane.coin);
					outtextxy(80+100,350+20,s1);
					putimage(80,350,&img_coin1);
					continue;
				}
				else if(tem_mod==3)
				{
					cyclooctane.jud_skin3=true;
					cyclooctane.coin-=20;
					cyclooctane.write_data();
					putimage(1100,750,&img_empt);
					putimage(300,370,&img_empt);
					LOGFONT f;
					gettextstyle(&f); 
					_tcscpy(f.lfFaceName, _T("黑体"));   
					f.lfQuality = ANTIALIASED_QUALITY;  
					f.lfHeight = 35;  
					f.lfWidth=20;
					settextstyle(&f);   
					settextcolor(RGB(255,255,0));
					TCHAR s1[10]; 
					_stprintf(s1,_T("金币：%d"),cyclooctane.coin);
					outtextxy(80+100,350+20,s1);
					putimage(80,350,&img_coin1);
					continue;
				}
			}
			else if(aaa=='a'||aaa=='d')
			{
				if(aaa=='a')
					tem_mod=tem_mod>1?tem_mod-1:3;
				if(aaa=='d')
					tem_mod=tem_mod<3?tem_mod+1:1;
				
			}
			setlinestyle(PS_SOLID, 1); setlinecolor(RGB(0,0,0));
			setfillcolor(RGB(0,0,0));
			fillellipse(310,690,325,700);
			fillellipse(760,690,775,700);
			fillellipse(1200,690,1215,700);
		}
		setlinestyle(PS_SOLID, 1); setlinecolor(RGB(255,0,0));
		setfillcolor(RGB(255,0,0));
		if(tem_mod==1)
			fillellipse(310,690,325,700);
		else if(tem_mod==2)
			fillellipse(760,690,775,700);
		else 
			fillellipse(1200,690,1215,700);
		FlushBatchDraw();
	}
	EndBatchDraw();
	cyclooctane.ben.mod=tem_mod;
	cyclooctane.ben.set_new_data(cyclooctane.ben.mod);
	cyclooctane.write_data();
	Game::clear();
	FSM::current=transition(gamestatus);
}

State* MENU_SKILL::transition(int x)  
{  
    switch(x)  
    {  
        case 2:  
            return &s2;  
		case 3:  
            return &s3;  
        default:  
            return &s8;  
    }  
}  
void MENU_SKILL::eventt()
{
	cyclooctane.read_data();
	settextstyle(80,40,_T("方正姚体"));  settextcolor(RGB(255,255,255));
	LPCTSTR str_c1=L"抽取";
	LPCTSTR str_c2=L"重新抽取 ( $ 5 )";
	LPCTSTR str_c3=L"完成";
	LPCTSTR str_c4=L"恭喜获得：";
	LPCTSTR str_ski1=L"子弹",str_ski2=L"旋转",str_ski3=L"穿透激光",str_ski4=L"即死激光",str_ski5=L"爆弹",str_ski6=L"食弹";
	LPCTSTR str_title=L"抽取初始技能";
	int gamestatus=1;
	int tem_state=1;
	BeginBatchDraw();
	setlinestyle(PS_SOLID, 1); setlinecolor(RGB(255,0,0));
	setfillcolor(RGB(255,0,0));
	fillellipse(460,630,460+15,630+10);
	//fillellipse(460,730,460+15,730+10);
	setbkcolor(RGB(0,0,0));
	settextstyle(110,40,_T("微软雅黑"));  settextcolor(RGB(255,255,255));
	outtextxy(500,150,str_title);
	settextstyle(60,35,_T("方正姚体"));  settextcolor(RGB(255,255,255));
	outtextxy(480,600,str_c1);
	outtextxy(480,700,str_c2);
	outtextxy(480,800,str_c3);
	LOGFONT f;
	gettextstyle(&f); 
	_tcscpy(f.lfFaceName, _T("黑体"));   
	f.lfQuality = ANTIALIASED_QUALITY;  
	f.lfHeight = 35;  
	f.lfWidth=20;
	settextstyle(&f);   
	TCHAR s1[10]; 
	settextcolor(RGB(255,255,0));
	_stprintf(s1,_T("金币：%d"),cyclooctane.coin);
	outtextxy(80+100,350+420,s1);
	putimage(80,350+400,&img_coin1);
	FlushBatchDraw();
	while(1)	
	{
		BeginBatchDraw();
		if(GetAsyncKeyState(VK_ESCAPE)<0)
		{	
			gamestatus=2;
			break;
		}
		if(_kbhit())
		{
			char aaa=_getch();
			if(aaa=='\r') 
			{	
				if(cyclooctane.flag==0)
				{
					if(tem_state!=1) 
					{	
						tem_state=1;
						continue;
					}
					cyclooctane.flag=1;
					cyclooctane.ben.ski[0]=rand()%6+1;
					f.lfHeight = 50;   f.lfWidth=28;  settextstyle(&f);   
					settextcolor(RGB(255,255,0));
					outtextxy(480,400,str_c4);
					putimage(760,400,&img_empt);
					switch(cyclooctane.ben.ski[0])
					{
					case 1: outtextxy(760,400,str_ski1); putimage(800,500,&img_ski1); break;
					case 2: outtextxy(760,400,str_ski2); putimage(800,500,&img_ski2);break;
					case 3: outtextxy(760,400,str_ski3); putimage(800,500,&img_ski3);break;
					case 4: outtextxy(760,400,str_ski4); putimage(800,500,&img_ski4);break;
					case 5: outtextxy(760,400,str_ski5); putimage(800,500,&img_ski5);break;
					case 6: outtextxy(760,400,str_ski6); putimage(800,500,&img_ski6); break;
					}
					cyclooctane.write_data();
				}
				else
				{
					if(tem_state==1 || (tem_state==2&&(cyclooctane.coin<5)))
					{
						tem_state=3;
						continue;
					}
					if(tem_state==3)
					{
						gamestatus=3;
						break;
					}
					if(cyclooctane.coin>=5)
					{
						int ccc=cyclooctane.ben.ski[0];
						while(ccc==cyclooctane.ben.ski[0])
						{
							ccc=rand()%6+1;
						}
						cyclooctane.ben.ski[0]=ccc;
						f.lfHeight = 50;   f.lfWidth=28;  settextstyle(&f);   
						settextcolor(RGB(255,255,0));
						outtextxy(480,400,str_c4);
						putimage(760,400,&img_empt);
						switch(cyclooctane.ben.ski[0])
						{
						case 1: outtextxy(760,400,str_ski1); putimage(800,500,&img_ski1); break;
						case 2: outtextxy(760,400,str_ski2); putimage(800,500,&img_ski2);break;
						case 3: outtextxy(760,400,str_ski3); putimage(800,500,&img_ski3);break;
						case 4: outtextxy(760,400,str_ski4); putimage(800,500,&img_ski4);break;
						case 5: outtextxy(760,400,str_ski5); putimage(800,500,&img_ski5);break;
						case 6: outtextxy(760,400,str_ski6); putimage(800,500,&img_ski6); break;
						}
						cyclooctane.coin-=5;
						f.lfHeight = 35;  
						f.lfWidth=20;
						settextstyle(&f);   
						TCHAR s1[10]; 
						_stprintf(s1,_T("金币：%d"),cyclooctane.coin);
						putimage(290,340+420,100,100,&img_empt,0,0);
						outtextxy(80+100,350+420,s1);
						cyclooctane.write_data();
					}
				}
				
			}
			if(aaa=='s'||aaa=='w')
			{
				if(aaa=='w')
					tem_state=tem_state>1?tem_state-1:3;
				if(aaa=='s')
					tem_state=tem_state<3?tem_state+1:1;
			}
		}
		if(cyclooctane.flag!=0)
		{
			f.lfHeight = 50;   f.lfWidth=28;  settextstyle(&f);   
			settextcolor(RGB(255,255,0));
			outtextxy(480,400,str_c4);
			putimage(760,400,&img_empt);
			switch(cyclooctane.ben.ski[0])
			{
			case 1: outtextxy(760,400,str_ski1); putimage(800,500,&img_ski1); break;
			case 2: outtextxy(760,400,str_ski2); putimage(800,500,&img_ski2);break;
			case 3: outtextxy(760,400,str_ski3); putimage(800,500,&img_ski3);break;
			case 4: outtextxy(760,400,str_ski4); putimage(800,500,&img_ski4);break;
			case 5: outtextxy(760,400,str_ski5); putimage(800,500,&img_ski5);break;
			case 6: outtextxy(760,400,str_ski6); putimage(800,500,&img_ski6); break;
			}
		}
		setlinestyle(PS_SOLID, 1); setlinecolor(RGB(0,0,0));
		setfillcolor(RGB(0,0,0));
		fillellipse(460,630,460+15,630+10);
		fillellipse(460,730,460+15,730+10);
		fillellipse(460,830,460+15,830+10);
		setlinestyle(PS_SOLID, 1); setlinecolor(RGB(255,0,0));
		setfillcolor(RGB(255,0,0));
		if(tem_state==1)
			fillellipse(460,630,460+15,630+10);
		else if(tem_state==2)
			fillellipse(460,730,460+15,730+10);
		else if(tem_state==3)
			fillellipse(460,830,460+15,830+10);

		FlushBatchDraw();
	}
	EndBatchDraw();
	cyclooctane.ben.cur=0;
	cyclooctane.room.new_room(1);
	cyclooctane.write_data();
	Game::clear();
	FSM::current=transition(gamestatus);
}

State* ON_GAME::transition(int x)  
{  
    switch(x)  
    {  
        case 4:  
            return &s4;  
        case 5:  
            return &s5;  
		case 7:
			return &s7;
        default:  
            return &s3; 
    }  
}  
void ON_GAME::eventt()
{
	int gamestatus=3;
	cyclooctane.on_game=true;
	Game::clear();
	while(1)  //  游戏循环执行
	{
/*		
		clock_t start,finish;
		double totaltime;
		start=clock();
*/
		BeginBatchDraw();
		Game::clear();
		cyclooctane.show();   // 显示画面
		cyclooctane.updateWithInput();    // 与输入有关的更新
		cyclooctane.updateWithoutInput();  // 与输入无关的更新
		cyclooctane.show();
/*
		finish=clock();
		totaltime=(double)(finish-start)/CLOCKS_PER_SEC;
		cout<<"\n此程序的运行时间为"<<totaltime<<"秒！"<<endl;
*/
		
		FlushBatchDraw();
		Sleep(50);
		if( GetAsyncKeyState(VK_ESCAPE)<0 )
		{
			gamestatus=4; break;
		}
		if(cyclooctane.ben.life_now<=0)
		{
			cyclooctane.coin+=cyclooctane.room_count-1;
			cyclooctane.on_game=false;
			gamestatus=5; break;
		}
		if(cyclooctane.room_count%3==0&&cyclooctane.room_count&&cyclooctane.judge_update==0)
		{
			cyclooctane.judge_update=1;
			gamestatus=7; break;
		}

	}
	EndBatchDraw();
	Game::clear();
	FSM::current=transition(gamestatus);
	return;
} 

State* MENU_PAUSE::transition(int x)  
{  
    switch(x)  
    {  
        case 1:  
            return &s1;  
        case 3:  
            return &s3;  
        default:  
            return &s4;  
    }  
}  
void MENU_PAUSE::eventt()
{
	int gamestatus=4;
	int tem_status=1;
	Game::clear();
	LPCTSTR str_continue=L"Continue";
	LPCTSTR str_save=L"Save";
	LPCTSTR str_exit=L"Exit";
	LPCTSTR str_pause=L"Pause";
	setbkcolor(RGB(0,0,0));
	setlinestyle(PS_SOLID, 1); setlinecolor(RGB(255,0,0));
	setfillcolor(RGB(255,0,0));
	fillellipse(575,535,585,545);
	while(1)	
	{
		settextstyle(160,60,_T("微软雅黑"));  settextcolor(RGB(255,255,255));
		outtextxy(550,200,str_pause);
		settextstyle(80,40,_T("方正姚体"));  settextcolor(RGB(255,255,255));
		outtextxy(600,500,str_continue);
		outtextxy(665,600,str_save);
		outtextxy(680,700,str_exit);
		if(_kbhit())
		{
			char aaa=_getch();
			if(aaa=='\r') break;
			if(aaa=='s'||aaa=='w')
			{
				if(aaa=='w')
					tem_status=tem_status>1?tem_status-1:3;
				if(aaa=='s')
					tem_status=tem_status<3?tem_status+1:1;
				setlinestyle(PS_SOLID, 1); setlinecolor(RGB(0,0,0));
				setfillcolor(RGB(0,0,0));
				fillellipse(575,535,585,545);
				fillellipse(640,635,650,645);
				fillellipse(655,735,665,745);
			}
		}
		setlinestyle(PS_SOLID, 1); setlinecolor(RGB(255,0,0));
		setfillcolor(RGB(255,0,0));
		if(tem_status==1)
		{fillellipse(575,535,585,545);}
		else if(tem_status==2)
		{fillellipse(640,635,650,645);}
		else {fillellipse(655,735,665,745);}
	}
	if( tem_status==1  ) 
		gamestatus=3;
	else if( tem_status==2)
	{
		gamestatus=3;
		cyclooctane.write_data();
	}
	else if( tem_status==3 ) 
		gamestatus=1;
	Game::clear();
	FSM::current=transition(gamestatus);
} 

State* MENU_DEAD::transition(int x)  
{  
    switch(x)  
    {  
        case 1:  
            return &s1;  
        case 6:  
            return &s6;  
        default:  
            return &s5;  
    }  
}  
void MENU_DEAD::eventt()
{
	int gamestatus=4;
	int tem_status=1;
	Game::clear();
	LPCTSTR str_restart=L"Restart";
	LPCTSTR str_exit=L"Exit";
	LPCTSTR str_title=L"You Died";
	LPCTSTR str_score=L"Score : ";
	LPCTSTR str_judge;
	int num_judge=0;
	if(cyclooctane.room_count<10)
	{	str_judge=L"Level : Weak";  num_judge=12;}
	else if(cyclooctane.room_count<30)
	{	str_judge=L"Level : Good"; num_judge=12;}
	else if(cyclooctane.room_count<100)
	{	str_judge=L"Level : Fantastic"; num_judge=17;}
	else 
	{	str_judge=L"Level：???"; num_judge=11;}
	setbkcolor(RGB(0,0,0));
	settextcolor(RGB(255,255,255));
	setlinestyle(PS_SOLID, 1); setlinecolor(RGB(255,0,0));
	setfillcolor(RGB(255,0,0));
	fillellipse(610,615,620,625);
	int score=cyclooctane.room_count; 
	TCHAR str_sc[10];
	_stprintf(str_sc,_T("%d"),score);
	cyclooctane.flag=0;
	cyclooctane.write_data();
	while(1)	
	{
		settextstyle(160,60,_T("微软雅黑"));  settextcolor(RGB(255,255,255));
		outtextxy(500,200,str_title);
		settextstyle(40,15,_T("微软雅黑"));  settextcolor(RGB(255,255,255));
		outtextxy(650,400,str_score);
		outtextxy(650,450,str_judge);
		outtextxy(780,401,str_sc);
		settextstyle(80,40,_T("方正姚体"));  settextcolor(RGB(255,255,255));
		outtextxy(640,580,str_restart);
		outtextxy(695,680,str_exit);
		if(_kbhit())
		{
			char aaa=_getch();
			if(aaa=='\r') break;
			if(aaa=='s'||aaa=='w')
			{
				if(aaa=='w')
					tem_status=tem_status>1?tem_status-1:2;
				if(aaa=='s')
					tem_status=tem_status<2?tem_status+1:1;
				setlinestyle(PS_SOLID, 1); setlinecolor(RGB(0,0,0));
				setfillcolor(RGB(0,0,0));
				fillellipse(610,615,620,625);
				fillellipse(665,715,675,725);
			}
		}
		setlinestyle(PS_SOLID, 1); setlinecolor(RGB(255,0,0));
		setfillcolor(RGB(255,0,0));
		if(tem_status==1)
			fillellipse(610,615,620,625);
		else if(tem_status==2)
			fillellipse(665,715,675,725);
	}
	switch(tem_status)
	{
	case 1: gamestatus=1; break;
	case 2: gamestatus=6; break;
	}
	
	Game::clear();
	FSM::current=transition(gamestatus);
} 

State* EXIT::transition(int)  
{  
    return NULL;  
}  
void EXIT::eventt()
{
	exit(0);
} 

State* SHOP1::transition(int x)  
{  
    switch(x)  
    {  
        case 3:  
            return &s3;
		case 9:
			return &s9;
        default:  
            return &s7;  
    }  
}  
void SHOP1::eventt()
{
	////////////////////////////////////////
	cyclooctane.death_count=9999;
	////////////////////////////////////////

	BeginBatchDraw();
	settextstyle(80,40,_T("方正姚体"));  settextcolor(RGB(255,255,255));
	LPCTSTR str_title=L"Update";
	LPCTSTR str_choice1=L"升级人物属性";
	LPCTSTR str_choice2=L"购买、替换技能";
//	LPCTSTR str_choice3=L"升级技能";
	LOGFONT f;
	gettextstyle(&f); 
	_tcscpy(f.lfFaceName, _T("黑体"));   
	f.lfQuality = ANTIALIASED_QUALITY;  
	settextstyle(&f);            
	f.lfHeight = 35;  
	f.lfWidth=20;
	settextstyle(&f);   
	TCHAR s1[10]; 
	_stprintf(s1,_T("灵魂：%d"),cyclooctane.death_count);
	outtextxy(80+100,50+320,s1);
	putimage(80,50+300,&img_coin2);

	int gamestatus=7;
	int tem_mod=1;
	setlinestyle(PS_SOLID, 1); setlinecolor(RGB(255,0,0)); setfillcolor(RGB(255,0,0));
	fillellipse(530,495,530+15,495+10);
//	fillellipse(530,625,530+15,625+10);
//	fillellipse(530,755,530+15,755+10);
	setbkcolor(RGB(0,0,0));
	settextstyle(160,60,_T("微软雅黑"));  settextcolor(RGB(255,255,255));
	outtextxy(530,100,str_title); 
	settextstyle(70,35,_T("黑体"));  settextcolor(RGB(255,255,255));
	outtextxy(570,470,str_choice1);
	outtextxy(570,600,str_choice2); 
//	outtextxy(570,730,str_choice3); 
	FlushBatchDraw();
	while(1)	
	{
		BeginBatchDraw();
		if(_kbhit())
		{
			char aaa=_getch();
			if(aaa==27) 
			{
				gamestatus=3;break;
			}
			if(aaa=='\r') 
			{
				gamestatus=9;break;
			}
			if(aaa=='w'||aaa=='s')
			{
				if(aaa=='w')
					tem_mod=tem_mod>1?tem_mod-1:2;
				if(aaa=='s')
					tem_mod=tem_mod<2?tem_mod+1:1;
				setlinestyle(PS_SOLID, 1); setlinecolor(RGB(0,0,0));
				setfillcolor(RGB(0,0,0));
				fillellipse(530,495,530+15,495+10);
				fillellipse(530,625,530+15,625+10);
		//		fillellipse(530,755,530+15,755+10);
			}
		}
		setlinestyle(PS_SOLID, 1); setlinecolor(RGB(255,0,0));
		setfillcolor(RGB(255,0,0));
		if(tem_mod==1)
			fillellipse(530,495,530+15,495+10);
		else if(tem_mod==2)
			fillellipse(530,625,530+15,625+10);
	//	else 
	//		fillellipse(530,755,530+15,755+10);
		FlushBatchDraw();
	}
	EndBatchDraw();
	Game::clear();
	shop_transport=tem_mod;
	FSM::current=transition(gamestatus);
	return;
}

State* SHOP2::transition(int x)  
{  
    switch(x)  
    {
        case 3:  return &s3; 
		case 7:  return &s7;
        default:  return &s9;  
    }
}  
void SHOP2::eventt()
{
	BeginBatchDraw();
	int gamestatus=9;
	int tem=1;
	FlushBatchDraw();
	LPCTSTR str_title1=L"升级人物属性";
	LPCTSTR str_title2=L"购买、替换技能";
	LPCTSTR str_ski_c0=L"a、d在已有技能中切换，w、s在商店技能中切换";

	LPCTSTR str_cha_c1=L"恢复所有生命 ($50)";
	LPCTSTR str_cha_c2=L"+2最大生命 ($100)";
	LPCTSTR str_cha_c3=L"+2移动速度 ($70)";

	LPCTSTR str_ski1=L"子弹";
	LPCTSTR str_ski2=L"旋转";
	LPCTSTR str_ski3=L"穿透激光";
	LPCTSTR str_ski4=L"即死激光";
	LPCTSTR str_ski5=L"爆弹";
	LPCTSTR str_ski6=L"食弹";

	LOGFONT f;
	gettextstyle(&f); 
	_tcscpy(f.lfFaceName, _T("黑体"));   
	f.lfQuality = ANTIALIASED_QUALITY;         
	f.lfHeight = 35;  
	f.lfWidth=20;
	settextstyle(&f);   
	TCHAR s1[10]; 
	_stprintf(s1,_T("灵魂：%d"),cyclooctane.death_count);
	outtextxy(80+100,50+320,s1);
	putimage(80,50+300,&img_coin2);
if(shop_transport==1)
{
	settextstyle(120,45,_T("微软雅黑"));  settextcolor(RGB(255,255,255));
	outtextxy(510,130,str_title1); 
	settextstyle(60,30,_T("黑体"));  settextcolor(YELLOW);
	outtextxy(570,470,str_cha_c1);
	outtextxy(570,570,str_cha_c2);
	outtextxy(570,670,str_cha_c3);
	setlinestyle(PS_SOLID, 1); setlinecolor(RGB(255,0,0)); setfillcolor(RGB(255,0,0));
	fillellipse(530,495,530+15,495+10);
//	fillellipse(530,595,530+15,595+10);
//	fillellipse(530,695,530+15,695+10);
	while(1)
	{
		BeginBatchDraw();
		if(_kbhit())
		{
			char cc=getch();
			if(cc==27)
			{
				gamestatus=7;
				break;
			}
			if(cc=='w')
				tem=tem>1?tem-1:3;
			if(cc=='s')
				tem=tem<3?tem+1:1;
			if(cc=='\r')
			{
				if(tem==1&&cyclooctane.death_count>=50)
				{
					cyclooctane.death_count-=50;
					cyclooctane.ben.life_now=cyclooctane.ben.life;
				}
				else if(tem==2&&cyclooctane.death_count>=100)
				{
					cyclooctane.death_count-=100;
					cyclooctane.ben.life+=2;
					cyclooctane.ben.life_now+=2;
				}
				else if(tem==3&&cyclooctane.death_count>=70)
				{
					cyclooctane.death_count-=70;
					cyclooctane.ben.speed+=2;
				}
			}

		}
		putimage(300,370,&img_empt);
		gettextstyle(&f); 
		_tcscpy(f.lfFaceName, _T("黑体"));   
		f.lfQuality = ANTIALIASED_QUALITY;         
		f.lfHeight = 35;  
		f.lfWidth=20;
		settextstyle(&f);   settextcolor(RGB(255,255,255));
		TCHAR s1[10]; 
		_stprintf(s1,_T("灵魂：%d"),cyclooctane.death_count);
		outtextxy(80+100,50+320,s1);
		putimage(80,50+300,&img_coin2);
		
		setlinestyle(PS_SOLID, 1); setlinecolor(RGB(0,0,0)); setfillcolor(RGB(0,0,0));
		fillellipse(530,495,530+15,495+10);
		fillellipse(530,595,530+15,595+10);
		fillellipse(530,695,530+15,695+10);
		setlinestyle(PS_SOLID, 1); setlinecolor(RGB(255,0,0)); setfillcolor(RGB(255,0,0));
		switch(tem)
		{
		case 1: fillellipse(530,495,530+15,495+10); break;
		case 2: fillellipse(530,595,530+15,595+10); break;
		case 3: fillellipse(530,695,530+15,695+10); break;
		}
		FlushBatchDraw();
	}
}
else if(shop_transport==2)
{
	int tem1=1,tem2=1;
	settextstyle(120,45,_T("微软雅黑"));  settextcolor(RGB(255,255,255));
	outtextxy(480,130,str_title2); 
	settextstyle(40,15,_T("微软雅黑"));  settextcolor(RGB(0,255,255));
	outtextxy(480,300,str_ski_c0);
	IMAGE img_tem;
	getimage(&img_tem,0,0,180,150);
	LPCTSTR str_shop_ski1=L"子弹：$200";
	LPCTSTR str_shop_ski2=L"旋转：$220";
	LPCTSTR str_shop_ski3=L"穿透激光：$250";
	LPCTSTR str_shop_ski4=L"即死激光：$250";
	LPCTSTR str_shop_ski5=L"爆弹：$230";
	LPCTSTR str_shop_ski6=L"食弹：$250";
	setlinestyle(PS_SOLID, 1); setlinecolor(RGB(255,0,0)); setfillcolor(RGB(255,0,0));
	fillellipse(150,760,150+15,760+10);
//	fillellipse(340,760,340+15,760+10);
	settextcolor(RGB(255,255,0));
	putimage(650,400,&img_ski1);   putimage(1100,400,&img_ski4);
	putimage(650,550,&img_ski2);   putimage(1100,550,&img_ski5);
	putimage(650,700,&img_ski3);   putimage(1100,700,&img_ski6);
	outtextxy(780,430,str_shop_ski1);  outtextxy(1230,430,str_shop_ski4);
	outtextxy(780,580,str_shop_ski2);  outtextxy(1230,580,str_shop_ski5);
	outtextxy(780,730,str_shop_ski3);  outtextxy(1230,730,str_shop_ski6);
	fillellipse(650-30,400+40,650-15,400+50); 
//	fillellipse(1100-30,400+40,1100-15,400+50);
//	fillellipse(650-30,550+40,650-15,550+50); 
//	fillellipse(1100-30,550+40,1100-15,550+50);
//	fillellipse(650-30,700+40,650-15,700+50); 
//	fillellipse(1100-30,700+40,1100-15,700+50);
	while(1)
	{
		BeginBatchDraw();
		if(_kbhit())
		{
			char cc=getch();
			if(cc==27)
			{
				gamestatus=7;
				break;
			}
			if(cc=='a')
				if(cyclooctane.ben.ski[1]!=0)
				{
					if(tem1==1) tem1=2;
					else tem1=1;
				}
			if(cc=='d')
			{	
				if(cyclooctane.ben.ski[1]!=0)
				{
					if(tem1==2) tem1=1;
					else tem1=2;
				}
			}
			if(cc=='w')
				tem2=tem2>1?tem2-1:6;
			if(cc=='s')
				tem2=tem2<6?tem2+1:1;
			if(cc=='\r')
			{
				if( tem2!=cyclooctane.ben.ski[0] && tem2!=cyclooctane.ben.ski[1] )
				{
					if( (tem2==1&&cyclooctane.death_count>=200) || (tem2==2&&cyclooctane.death_count>=220) || (tem2==3&&cyclooctane.death_count>=250) || (tem2==4&&cyclooctane.death_count>=250) || (tem2==5&&cyclooctane.death_count>=230) || (tem2==6&&cyclooctane.death_count>=250))
					{
						if(cyclooctane.ben.ski[1]==0)
						{
							cyclooctane.ben.ski[1]=tem2;
						}
						else
						{
							cyclooctane.ben.ski[tem1-1]=tem2;
						}
						cyclooctane.death_count-=200;
						if(tem2==3||tem2==4||tem2==6)
							cyclooctane.death_count-=50;
						if(tem2==2)
							cyclooctane.death_count-=20;
						if(tem2==5)
							cyclooctane.death_count-=30;
					}
				}
			}
		}
		setlinestyle(PS_SOLID, 1); setlinecolor(RGB(0,0,0)); setfillcolor(RGB(0,0,0));
		fillellipse(150,760,150+15,760+10);
		fillellipse(340,760,340+15,760+10);
		fillellipse(650-30,400+40,650-15,400+50); 
		fillellipse(1100-30,400+40,1100-15,400+50);
		fillellipse(650-30,550+40,650-15,550+50); 
		fillellipse(1100-30,550+40,1100-15,550+50);
		fillellipse(650-30,700+40,650-15,700+50); 
		fillellipse(1100-30,700+40,1100-15,700+50);
		putimage(100,600,&img_tem);
		putimage(300,600,&img_tem);
		putimage(300,370,&img_empt);
		gettextstyle(&f); 
		_tcscpy(f.lfFaceName, _T("黑体"));   
		f.lfQuality = ANTIALIASED_QUALITY;         
		f.lfHeight = 35;  
		f.lfWidth=20;
		settextstyle(&f);   settextcolor(RGB(255,255,255));
		TCHAR s1[10]; 
		_stprintf(s1,_T("灵魂：%d"),cyclooctane.death_count);
		outtextxy(80+100,50+320,s1);
		putimage(80,50+300,&img_coin2);
		setlinestyle(PS_SOLID, 1); setlinecolor(RGB(255,0,0)); setfillcolor(RGB(255,0,0));
		switch(tem1)
		{
		case 1: fillellipse(150,760,150+15,760+10); break;
		case 2: fillellipse(340,760,340+15,760+10); break;
		}
		switch(tem2)
		{
		case 1: fillellipse(650-30,400+40,650-15,400+50);  break;
		case 2: fillellipse(650-30,550+40,650-15,550+50); break;
		case 3: fillellipse(650-30,700+40,650-15,700+50);  break;
		case 4: fillellipse(1100-30,400+40,1100-15,400+50); break;
		case 5: fillellipse(1100-30,550+40,1100-15,550+50); break;
		case 6: fillellipse(1100-30,700+40,1100-15,700+50); break;
		}
		settextcolor(RGB(255,50,255));
		switch(cyclooctane.ben.ski[0])
		{
		case 1: outtextxy(120,710,str_ski1); putimage(100,600,&img_ski1); break;
		case 2: outtextxy(110,710,str_ski2); putimage(100,600,&img_ski2);break;
		case 3: outtextxy(100,710,str_ski3); putimage(100,600,&img_ski3);break;
		case 4: outtextxy(100,710,str_ski4); putimage(100,600,&img_ski4);break;
		case 5: outtextxy(120,710,str_ski5); putimage(100,600,&img_ski5);break;
		case 6: outtextxy(120,710,str_ski6); putimage(100,600,&img_ski6); break;
		}
		switch(cyclooctane.ben.ski[1])
		{
		case 0: putimage(300,600,&img_ski_null); break;
		case 1: outtextxy(320,710,str_ski1); putimage(300,600,&img_ski1); break;
		case 2: outtextxy(310,710,str_ski2); putimage(300,600,&img_ski2);break;
		case 3: outtextxy(300,710,str_ski3); putimage(300,600,&img_ski3);break;
		case 4: outtextxy(300,710,str_ski4); putimage(300,600,&img_ski4);break;
		case 5: outtextxy(320,710,str_ski5); putimage(300,600,&img_ski5);break;
		case 6: outtextxy(320,710,str_ski6); putimage(300,600,&img_ski6); break;
		}
		FlushBatchDraw();
	}
}
	EndBatchDraw();
	Game::clear();
	cyclooctane.write_data();
	FSM::current=transition(gamestatus);
	return;
}

State* HELP::transition(int x)
{
    switch(x)  
    {
        case 1:  return &s1; 
        default:  return &s10;  
    }
}
void HELP::eventt()
{
	int gamestatus=10;
	int tem=1;
	while(1)
	{
		BeginBatchDraw();
		switch(tem)
		{
		case 1: putimage(250,50,&img_help1); break;
		case 2: putimage(250,50,&img_help2); break;
		case 3: putimage(250,50,&img_help3); break;
		case 4: putimage(250,50,&img_help4); break;
		case 5: putimage(250,50,&img_help5); break;
		case 6: putimage(250,50,&img_help6); break;
		case 7: putimage(250,50,&img_help7); break;
		case 8: putimage(250,50,&img_help8); break;
		}
		if(_kbhit())
		{
			char cc=getch();
			if(cc=='W'|| cc=='w')
				tem=tem>=2?tem-1:tem;
			if(cc=='s'|| cc=='S')
				tem=tem<=7?tem+1:tem;
			if(cc==27)
			{	
				gamestatus=1;
				break;
			}
		}
		FlushBatchDraw();
	}
	EndBatchDraw();
	Game::clear();
	FSM::current=transition(gamestatus);
	return;
}

/////////// Data Base ////////////////
void Game::fresh_data()
{
	empt.startup();
	Bullet_num_time_count=0;
	num_monster_fresh=0;
	judge_update=0;
	death_count=0;
	coin=0;
	flag=0;
	on_game=false;
	jud_skin2=false;
	jud_skin3=false;
	return;
}
/*
bool Game::read_data()
{
	/*Decrypt_file("save01.data", "save03.data");
	//FILE *fp=fopen("save01.txt","rb");
	ifstream load_data("save01.data",ios::in);

	if(!load_data.is_open())
		return false;
	fread( &square,sizeof(struct Square),1,fp );  
	//fscanf(fp,"%c",&c);
	//assert(c=='a');
	fread( &ben.mod,sizeof(int),1,fp );
	fread( &ben.pos_x,sizeof(double),1,fp );
	fread( &ben.pos_y,sizeof(double),1,fp );
	fread( &ben.judge_dir,sizeof(int),1,fp );
	fread( &ben.judge_hurt,sizeof(ben.judge_hurt),1,fp );
	fread( &ben.line,sizeof(ben.line) ,1,fp);
	fread( &ben.last_line,sizeof(ben.last_line) ,1,fp);
	fread( &ben.special,sizeof(ben.special),1,fp );
	fread( &ben.last_special,sizeof(ben.last_special),1,fp );
	fread( &ben.num_bul,sizeof(ben.num_bul),1,fp );
	fread( &ben.speed,sizeof(ben.speed),1,fp );
	fread( &ben.life,sizeof(ben.life),1,fp );
	fread( &ben.life_now,sizeof(ben.life_now) ,1,fp);
	fread( &ben.print_chara,sizeof(ben.print_chara),1,fp );
	fread( &ben.ski,sizeof(ben.ski) ,1,fp);
	fread( &ben.cur,sizeof(ben.cur),1,fp );
	fread( &ben.num_count,sizeof(ben.num_count),1,fp );
// 	fscanf(fp,"%c",&c);
// 	assert(c=='b');
	fread( &(current_state),sizeof(current_state) ,1,fp);
	fread( &(judge_update),sizeof(judge_update) ,1,fp);
	fread( &(death_count),sizeof(death_count),1,fp );
	fread( &(Bullet_num_time_count),sizeof(Bullet_num_time_count) ,1,fp);
	fread( &(num_monster_fresh),sizeof(num_monster_fresh),1,fp );
	fread( &(room_count),sizeof(room_count) ,1,fp);
	fread( &(coin),sizeof(coin) ,1,fp);
	fread( &(flag),sizeof(flag),1,fp );
	fread( &(on_game),sizeof(on_game) ,1,fp);
	fread( &(jud_skin2),sizeof(jud_skin2),1,fp );
	fread( &(jud_skin3),sizeof(jud_skin3),1,fp );
// 	fscanf(fp,"%c",&c);
// 	assert(c=='c');
	fread( &room,sizeof(struct Room) ,1,fp);
// 	fscanf(fp,"%c",&c);
// 	assert(c=='d');
	//room.new_room(1);
	Bullet::num_time_count=Bullet_num_time_count;

	ben.head=new Bullet;
	ben.head->exist=false;
	ben.head->nex=NULL;
	ben.last=ben.head;
	Bullet *bul;
	for(int i=0; i<ben.num_bul; i++)
	{
		bul=new Bullet;
		fread( bul,sizeof(struct Bullet),1,fp );
		ben.last->nex=bul;
		ben.last=ben.last->nex;
	}
	ben.last->nex=NULL;
// 	fscanf(fp,"%c",&c);
// 	assert(c=='e');
	fclose(fp);
	/*ofstream te;
	int t1=0;
	te.open("save03.data", ios::out);
	te.write(&t1, sizeof(t1) );
	te.close();
	return true;
}
void Game::write_data()
{
//	FILE *fp;
//	fp=fopen("save01.txt","wb");
 	ofstream save_data("save01.data", ios::out|ios::binary);


	if(FSM::current==&s1) {current_state=1;}
	else if(FSM::current==&s2) {current_state=2;}
	else if(FSM::current==&s3) {current_state=3;}
	else if(FSM::current==&s4) {current_state=4;}
	else if(FSM::current==&s5) {current_state=5;}
	else if(FSM::current==&s7) {current_state=7;}
	else {current_state=6;}
	Bullet_num_time_count=Bullet::num_time_count;
	
	fwrite( &square,sizeof(struct Square),1,fp );
	//fprintf(fp,"%c",'a');

	fwrite( &ben.mod,sizeof(ben.mod) ,1,fp);
	fwrite( &ben.pos_x,sizeof(ben.pos_x),1,fp );
	fwrite( &ben.pos_y,sizeof(ben.pos_y),1,fp );
	fwrite( &ben.judge_dir,sizeof(ben.judge_dir),1,fp );
	fwrite( &ben.judge_hurt,sizeof(ben.judge_hurt),1,fp );
	fwrite( &ben.line,sizeof(ben.line),1,fp );
	fwrite( &ben.last_line,sizeof(ben.last_line) ,1,fp);
	fwrite( &ben.special,sizeof(ben.special),1,fp );
	fwrite( &ben.last_special,sizeof(ben.last_special) ,1,fp);
	fwrite( &ben.num_bul,sizeof(ben.num_bul),1,fp );
	fwrite( &ben.speed,sizeof(ben.speed),1,fp );
	fwrite( &ben.life,sizeof(ben.life),1,fp );
	fwrite( &ben.life_now,sizeof(ben.life_now),1,fp );
	fwrite( &ben.print_chara,sizeof(ben.print_chara) ,1,fp);
	fwrite( &ben.ski,sizeof(ben.ski),1,fp );
	fwrite( &ben.cur,sizeof(ben.cur),1,fp );
	fwrite( &ben.num_count,sizeof(ben.num_count),1,fp );
	/*fprintf(fp,"%c",'b');

	fwrite(&current_state, sizeof(current_state),1,fp );
	fwrite(&judge_update, sizeof(judge_update),1,fp );
	fwrite(&death_count, sizeof(death_count),1,fp );
	fwrite(&Bullet_num_time_count, sizeof(Bullet_num_time_count) ,1,fp);
	fwrite(&num_monster_fresh, sizeof(num_monster_fresh) ,1,fp);
	fwrite(&room_count, sizeof(room_count),1,fp );
	fwrite( &coin,sizeof(coin),1,fp );
	fwrite( &flag,sizeof(flag) ,1,fp);
	fwrite( &on_game,sizeof(on_game) ,1,fp);
	fwrite( &jud_skin2,sizeof(jud_skin2),1,fp );
	fwrite( &jud_skin3,sizeof(jud_skin3),1,fp );
/*	fprintf(fp,"%c",'c');
	
	fwrite( &room,sizeof(struct Room),1,fp );
	/*fprintf(fp,"%c",'d');

	Bullet *bul=ben.head->nex;
	for(int i=0; i<ben.num_bul; i++)
	{
		fwrite( bul,sizeof(struct Bullet),1,fp );
		bul=bul->nex;
	}
	fclose(fp);
	/*fprintf(fp,"%c",'e');
	/*Encrypt_file("save02.data","save01.data");
	ofstream te;
	int t1=0;
	te.open("save02.data", ios::out);
	te.write(&t1, sizeof(t1) );
	te.close();
	return;
}*/
bool Game::read_data()
{
	fstream load_data,de_data;
	de_data.open("save02.data",ios::in);
	if(!de_data.is_open())
		return false;
	Decrypt_file("save02.data","save01.data");
	de_data.close();
	load_data.open("save01.data",ios::in);

	
	///////// Total DATA ///////////
	load_data>>current_state>>judge_update
		>>death_count>>Bullet_num_time_count
		>>num_monster_fresh>>
		room_count>>coin>>flag>>on_game>>jud_skin2>>jud_skin3;

	///////// Square ////////////
	load_data>>square.pos_x>>square.pos_y
		>>square.angle>>square.init>>square.speed>>square.jud_way;
	square.new_room_point(square.pos_x,square.pos_y,square.angle,square.pos);
	//////// Room //////////
	load_data>>room.num_stab>>room.num_stone
		>>room.time_count>>room.rand_c>>room.time_max;
	for(int i=0 ; i<10 ; i++)
	{	
		load_data>>room.stab[i].pos_x>>room.stab[i].pos_y
			>>room.stab[i].count>>room.stab[i].init>>room.stab[i].judge_show
			>>room.stab[i].count_max;
		room.stab[i].new_point();
	}
	for(int i=0; i<10; i++)
	{
		load_data>>room.stone[i].pos_x>>room.stone[i].pos_y>>room.stab[i].init;
		room.stone[i].new_point();
	}
	for(int i=0; i<500; i++)
	{
		load_data>>room.monster[i].pos_x>>room.monster[i].pos_y
			>>room.monster[i].speed>>room.monster[i].num_edge
			>>room.monster[i].special>>room.monster[i].exist>>room.monster[i].special;
		room.monster[i].new_point(room.monster[i].pos_x,room.monster[i].pos_y,room.monster[i].num_edge,room.monster[i].pos);
	}
	///////// Charactor  //////////
	load_data>>ben.mod>>ben.pos_x>>ben.pos_y
		>>ben.judge_dir
		>>ben.judge_hurt>>ben.speed
		>>ben.life>>ben.life_now>>ben.num_bul
		>>ben.cur;
	for(int i=0; i<10; i++)
		load_data>>ben.num_count[i];
	for(int i=0; i<5; i++)
		load_data>>ben.ski[i];
	ben.new_point(ben.pos_x,ben.pos_y,ben.print_chara);

	load_data>>ben.line.pos_x>>ben.line.pos_y>>ben.line.xita
		>>ben.line.exist>>ben.line.life>>ben.line.special>>ben.line.cur;
	load_data>>ben.last_line.pos_x>>ben.last_line.pos_y>>ben.last_line.xita
		>>ben.last_line.exist>>ben.last_line.life>>ben.last_line.special>>ben.last_line.cur;
	load_data>>ben.special.pos_x>>ben.special.pos_y>>ben.special.xita
		>>ben.special.exist>>ben.special.special>>ben.special.life>>ben.special.cur;

	Bullet *tem=new Bullet,*pre=ben.head;
	int num_store_bul=0;
	load_data>>num_store_bul;
	while(num_store_bul--)
	{
		load_data>>tem->pos_x>>tem->pos_y
		>>tem->xita>>tem->exist>>tem->special
		>>tem->life>>tem->cur;

		pre->nex=tem;
		tem=new Bullet;
		pre=pre->nex;
	}
	delete tem;
	pre->nex=NULL;
	ben.last=pre;
	
	///////// end ///////////////
	load_data.close();
	de_data.open("save01.data",ios::out|ios::trunc);
	//de_data<<"111"<<endl;
	de_data.close();
	return true;
}
void Game::write_data()
{
	fstream save_data,en_data;
	save_data.open("save01.data",ios::out);
	
	if(FSM::current==&s1) {current_state=1;}
	else if(FSM::current==&s2) {current_state=2;}
	else if(FSM::current==&s3) {current_state=3;}
	else if(FSM::current==&s4) {current_state=4;}
	else if(FSM::current==&s5) {current_state=5;}
	else if(FSM::current==&s7) {current_state=7;}
	else {current_state=6;}
	///////// Total DATA ///////////
	save_data<<current_state<<endl<<judge_update<<endl
		<<death_count<<endl<<Bullet_num_time_count<<endl
		<<endl<<num_monster_fresh<<endl<<
		room_count<<endl<<coin<<endl<<flag<<endl<<on_game<<endl<<jud_skin2<<endl<<jud_skin3<<endl<<endl;

	///////// Square ////////////
	save_data<<square.pos_x<<endl<<square.pos_y<<endl
		<<square.angle<<endl<<square.init<<endl<<square.speed<<endl<<square.jud_way<<endl<<endl;

	//////// Room //////////
	save_data<<room.num_stab<<endl<<room.num_stone<<endl
		<<room.time_count<<endl<<room.rand_c<<endl<<room.time_max<<endl;
	for(int i=0 ; i<10 ; i++)
	{	
		save_data<<room.stab[i].pos_x<<endl<<room.stab[i].pos_y<<endl
			<<room.stab[i].count<<endl<<room.stab[i].init<<endl<<room.stab[i].judge_show<<endl
			<<room.stab[i].count_max<<endl;
	}
	for(int i=0; i<10; i++)
		save_data<<room.stone[i].pos_x<<endl<<room.stone[i].pos_y<<endl<<room.stab[i].init<<endl;
	for(int i=0; i<500; i++)
	{
		save_data<<room.monster[i].pos_x<<endl<<room.monster[i].pos_y<<endl
			<<room.monster[i].speed<<endl<<room.monster[i].num_edge<<endl
			<<room.monster[i].special<<endl<<room.monster[i].exist<<endl<<room.monster[i].special<<endl;
	}
	///////// Charactor  ////////////
	save_data<<ben.mod<<endl<<ben.pos_x<<endl<<ben.pos_y<<endl
		<<ben.judge_dir<<endl
		<<ben.judge_hurt<<endl<<ben.speed<<endl
		<<ben.life<<endl<<ben.life_now<<endl<<ben.num_bul<<endl
		<<ben.cur<<endl;
	for(int i=0; i<10; i++)
		save_data<<ben.num_count[i]<<endl;
	for(int i=0; i<5; i++)
		save_data<<ben.ski[i]<<endl;

	save_data<<ben.line.pos_x<<endl<<ben.line.pos_y<<endl<<ben.line.xita<<endl
		<<ben.line.exist<<endl<<ben.line.life<<endl<<ben.line.special<<endl<<ben.line.cur<<endl;
	save_data<<ben.last_line.pos_x<<endl<<ben.last_line.pos_y<<endl<<ben.last_line.xita<<endl
		<<ben.last_line.exist<<endl<<ben.last_line.life<<endl<<ben.last_line.special<<endl<<ben.last_line.cur<<endl;
	save_data<<ben.special.pos_x<<endl<<ben.special.pos_y<<endl<<ben.special.xita<<endl
		<<ben.special.exist<<endl<<ben.special.special<<endl<<ben.special.life<<endl<<ben.special.cur<<endl;

	Bullet *tem=ben.head->nex;
	int num_store_bul=0;
	while(tem!=NULL)
	{
		num_store_bul++;
		tem=tem->nex;
	}
	save_data<<num_store_bul<<endl;
	tem=ben.head->nex;
	while(tem!=NULL)
	{
		save_data<<tem->pos_x<<endl<<tem->pos_y<<endl
		<<tem->xita<<endl<<tem->exist<<endl<<tem->special<<endl
		<<tem->life<<endl<<tem->cur<<endl;
		tem=tem->nex;
	}
	///////// end ///////////////
	save_data.close();
	Encrypt_file("save01.data","save02.data");
	en_data.open("save01.data",ios::out|ios::trunc);
	//en_data<<"222"<<endl;
	en_data.close();
	return;
}

/////////// FSM ////////////////
void FSM::reset()  
{  
    current = &s1;  
}
void FSM::change(int n)
{
	switch(n)
	{
	case 1: current = &s1;  break;
	case 2: current = &s2;  break;
	case 4: current = &s4;  break;
	case 5: current = &s5;  break;
	case 6: current = &s6;  break;
	case 7: current = &s7;  break;
	case 8: current = &s8;  break;
	case 9: current = &s9;  break;
	default :current = &s3;  break;
	}
	return;
}


///////  DES ///////

int k[64]={
	0,0,0,0,1,0,1,0,
	0,0,1,0,1,0,0,1,
	1,0,1,0,1,1,1,0,
	0,1,0,1,0,0,1,1,
	0,1,1,0,0,1,1,0,
	1,1,0,1,0,1,1,1,
	0,1,1,0,0,1,0,0,
	1,1,1,1,0,1,0,0
};

int sub_k[16][64];

int IP[] ={  57,49,41,33,25,17,9,1,  
               59,51,43,35,27,19,11,3,  
               61,53,45,37,29,21,13,5,  
               63,55,47,39,31,23,15,7,  
               56,48,40,32,24,16,8,0,  
               58,50,42,34,26,18,10,2,  
               60,52,44,36,28,20,12,4,  
               62,54,46,38,30,22,14,6};  
// 结尾置换表  
int IP_1[] ={39,7,47,15,55,23,63,31,  
		      38,6,46,14,54,22,62,30,  
		     37,5,45,13,53,21,61,29,  
		      36,4,44,12,52,20,60,28,  
		      35,3,43,11,51,19,59,27,  
			   34,2,42,10,50,18,58,26,  
	         33,1,41,9,49,17,57,25,  
	         32,0,40,8,48,16,56,24}; 
// 密钥置换表，将64位密钥变成56位  
int PC_1[] = {56,48,40,32,24,16,8,  
              0,57,49,41,33,25,17,  
              9,1,58,50,42,34,26,  
              18,10,2,59,51,43,35,  
              62,54,46,38,30,22,14,  
              6,61,53,45,37,29,21,  
              13,5,60,52,44,36,28,  
              20,12,4,27,19,11,3
};   
// 压缩置换，将56位密钥压缩成48位子密钥  
int PC_2[] = {13,16,10,23,0,4,2,27,  
              14,5,20,9,22,18,11,3,  
              25,7,15,6,26,19,12,1,  
              40,51,30,36,46,54,29,39,  
              50,44,32,46,43,48,38,55,  
              33,52,45,41,49,35,28,31
};  
// 每轮左移的位数  
int shiftBits[] = {1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1};  

// 扩展置换表，将 32位 扩展至 48位  
int E[] = {
			31, 0, 1, 2, 3, 4,  
            3,  4, 5, 6, 7, 8,  
            7,  8,9,10,11,12,  
            11,12,13,14,15,16,  
            15,16,17,18,19,20,  
            19,20,21,22,23,24,  
            23,24,25,26,27,28,  
            27,28,29,30,31, 0
};  

int S_BOX[8][4][16] = {  
    {    
        {14,4,13,1,2,15,11,8,3,10,6,12,5,9,0,7},    
        {0,15,7,4,14,2,13,1,10,6,12,11,9,5,3,8},    
        {4,1,14,8,13,6,2,11,15,12,9,7,3,10,5,0},   
        {15,12,8,2,4,9,1,7,5,11,3,14,10,0,6,13}   
    },  
    {    
        {15,1,8,14,6,11,3,4,9,7,2,13,12,0,5,10},    
        {3,13,4,7,15,2,8,14,12,0,1,10,6,9,11,5},   
        {0,14,7,11,10,4,13,1,5,8,12,6,9,3,2,15},    
        {13,8,10,1,3,15,4,2,11,6,7,12,0,5,14,9}    
    },   
    {    
        {10,0,9,14,6,3,15,5,1,13,12,7,11,4,2,8},    
        {13,7,0,9,3,4,6,10,2,8,5,14,12,11,15,1},    
        {13,6,4,9,8,15,3,0,11,1,2,12,5,10,14,7},    
        {1,10,13,0,6,9,8,7,4,15,14,3,11,5,2,12}    
    },   
    {    
        {7,13,14,3,0,6,9,10,1,2,8,5,11,12,4,15},    
        {13,8,11,5,6,15,0,3,4,7,2,12,1,10,14,9},    
        {10,6,9,0,12,11,7,13,15,1,3,14,5,2,8,4},    
        {3,15,0,6,10,1,13,8,9,4,5,11,12,7,2,14}    
    },  
    {    
        {2,12,4,1,7,10,11,6,8,5,3,15,13,0,14,9},    
        {14,11,2,12,4,7,13,1,5,0,15,10,3,9,8,6},    
        {4,2,1,11,10,13,7,8,15,9,12,5,6,3,0,14},    
        {11,8,12,7,1,14,2,13,6,15,0,9,10,4,5,3}    
    },  
    {    
        {12,1,10,15,9,2,6,8,0,13,3,4,14,7,5,11},    
        {10,15,4,2,7,12,9,5,6,1,13,14,0,11,3,8},    
        {9,14,15,5,2,8,12,3,7,0,4,10,1,13,11,6},    
        {4,3,2,12,9,5,15,10,11,14,1,7,6,0,8,13}    
    },   
    {    
        {4,11,2,14,15,0,8,13,3,12,9,7,5,10,6,1},    
        {13,0,11,7,4,9,1,10,14,3,5,12,2,15,8,6},    
        {1,4,11,13,12,3,7,14,10,15,6,8,0,5,9,2},    
        {6,11,13,8,1,4,10,7,9,5,0,15,14,2,3,12}    
    },   
    {    
        {13,2,8,4,6,15,11,1,10,9,3,14,5,0,12,7},    
        {1,15,13,8,10,3,7,4,12,5,6,11,0,14,9,2},    
        {7,11,4,1,9,12,14,2,0,6,10,13,15,3,5,8},    
        {2,1,14,7,4,10,8,13,15,12,9,0,3,5,6,11}    
    }   
};  
int P[] = {
			15,6,19,20,28,11,27,16,  
            0,14,22,25,4,17,30,9,  
            1,7,23,13,31,26,2,8,  
            18,12,29,5,21,10,3,24
};  

int get_ten1(int *a, int fir, int las)
{
	int ans=0,po=1;
	for(int i=fir; i<=las; i++)
	{
		ans+=po*a[i];
		po*=2;
	}
	return ans;
}
int get_ten2(int a1, int a2)
{
	return a2*1+a1*2;
}

void f(int * r, int *k, int *ans)
{
	int r_tem[48],r_ans[32];
	for(int i=0; i<48; i++)
		r_tem[i]=r[E[i]];
	for(int i=0; i<48; i++)
		r_tem[i]^=k[i];
	for(int i=0 ; i<8; i++)   
	{
		int x=get_ten2(r_tem[i*6+0],r_tem[i*6+5]);
		int y=get_ten1(r_tem,i*6+1,i*6+4);
		int ans1=S_BOX[i][x][y];
		for(int j=i*4+3; j>=i*4+0; j--)
		{
			r_ans[j]=ans1%2;
			ans1/=2;
		}
	}
	for(int i=0; i<32; i++)
		ans[i]=r_ans[P[i]];
	return;
};
void initkey()
{
	int c[28],d[28],tem[64];
	//  2.  key
	for(int j=0; j<56; j++)
		tem[j]=k[PC_1[j]];
	for(int j=0; j<28; j++)
	{	
		c[j]=tem[j];
		d[j]=tem[j+28];
	}
	for(int i=0; i<16; i++)
	{
		for(int k=0; k<shiftBits[i]; k++)
		{
			int c1=c[0],d1=d[0];
			for(int j=27; j>0; j--)
			{
				c[j-1]=c[j];
				d[j-1]=d[j];
			}
			d[27]=d1; c[27]=c1;
		}
		for(int j=0; j<28; j++)
		{	
			tem[j]=c[j];
			tem[j+28]=d[j];
		}
		for(int j=0; j<48; j++)
			sub_k[i][j]=tem[PC_2[j]];
	}
}

void encrypt(char *s, char *ans)  //  s明文   ans 密文
{
	int ans1[64];
	for(int i=0; i<8; i++)
	{
		for(int j=0; j<8; j++)
		{
			ans1[i*8+j]=(s[i]>>j)&1;
		}
	}
	int s1[64];
	int l[32],r[32];
	//  1.  initial
	for(int i=0; i<64; i++)
		s1[i]=ans1[IP[i]];
	for(int i=0; i<32; i++)
	{	
		l[i]=s1[i];
		r[i]=s1[i+32];
	}
	initkey();
	// 4.
	for(int i=0; i<16; i++)
	{
		int ans_t[32],tem;
		f(r,sub_k[i],ans_t);
		for(int j=0; j<32; j++)
		{	
			tem=r[j];
			r[j]=l[j]^ans_t[j];
			l[j]=tem;
		}
	}
	for(int i=0; i<32; i++)
	{	
		s1[i]=r[i];
		s1[i+32]=l[i];
	}
	for(int i=0; i<64; i++)
		ans1[i]=s1[IP_1[i]];
	for(int i=0; i<8; i++)
	{
		int cc=get_ten1(ans1,i*8+0,i*8+7);
		ans[i]=cc;
	}
	return;
}
void decrypt(char *s, char *ans) //  s密文   ans 明文
{
	int ans1[64];
	for(int i=0; i<8; i++)
	{
		for(int j=0; j<8; j++)
		{
			ans1[i*8+j]=(s[i]>>j)&1;
		}
	}
	int s1[64];
	int l[32],r[32];
	//  1.  initial
	for(int i=0; i<64; i++)
		s1[i]=ans1[IP[i]];
	for(int i=0; i<32; i++)
	{	
		l[i]=s1[i];
		r[i]=s1[i+32];
	}
	// 4.
	for(int i=15; i>=0; i--)
	{
		int ans_t[32],tem;
		f(r,sub_k[i],ans_t);
		for(int j=0; j<32; j++)
		{	
			tem=r[j];
			r[j]=l[j]^ans_t[j];
			l[j]=tem;
		}
	}
	for(int i=0; i<32; i++)
	{	
		s1[i]=r[i];
		s1[i+32]=l[i];
	}
	for(int i=0; i<64; i++)
		ans1[i]=s1[IP_1[i]];
	for(int i=0; i<8; i++)
	{
		int cc=get_ten1(ans1,i*8+0,i*8+7);
		ans[i]=cc;
	}
	return;
}

int Encrypt_file(char *s_name,char *ans_name)
{  
    FILE *s,*ans;  
    int c;  
    char s1[8],s2[8];  
	s = fopen(s_name,"rb");
	ans = fopen(ans_name,"wb");
    while(!feof(s))
	{  
        if((c = fread(s1,sizeof(char),8,s)) == 8)
		{  
            encrypt(s1,s2);  
            fwrite(s2,sizeof(char),8,ans);    
        }  
    }  
    if(c)
	{  
        memset(s1 + c,'\0',7 - c);  
        s1[7] = 8 - c;  
        encrypt(s1,s2);  
        fwrite(s2,sizeof(char),8,ans);  
    }  
    fclose(s);  
    fclose(ans);  
    return 0;  
} 
int Decrypt_file(char *s_name, char *ans_name)
{  
    FILE *s, *ans;  
    int c,cc=0;
    long flen;  
    char s1[8],s2[8];  
    ans = fopen(s_name,"rb");
	s = fopen(ans_name,"wb");
    fseek(ans,0,SEEK_END);
    flen = ftell(ans);
    rewind(ans); 
    while(1)
	{  
        fread(s2,sizeof(char),8,ans);  
        decrypt(s2,s1);                         
        cc += 8;  
        if(cc < flen)
            fwrite(s1,sizeof(char),8,s);  
        else
            break;  
    } 
    if(s1[7] < 8)
        for(c = 8 - s1[7]; c < 7; c++)
            if(s1[c] != '\0')
                break;  
    if(c == 7)
        fwrite(s1,sizeof(char),8 - s1[7],s);  
    else 
        fwrite(s1,sizeof(char),8,s);  
    fclose(s);  
    fclose(ans);  
    return 0; 
}  
