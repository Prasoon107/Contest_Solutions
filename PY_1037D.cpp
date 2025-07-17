#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#define ll long long
#define ul unsigned long long
#define ld long double
#define pll pair<ll,ll>
#define pii pair<int,int>
#define vi vector<int>
#define vl vector<ll>
#define vpl vector<pll>
#define vpi vector<pii>
#define vvi vector<vi>
#define vvl vector<vl>
#define vb vector<bool>
#define vs vector<string>
#define rep(i,a,b) for(ll i=a;i<b;i++)
#define rrep(i,a,b) for(ll i=a;i>=b;i--)
#define frs(i,n) for(ll i=1;i*i<=n;i++)
#define fr(i,a,b,c) for(ll i=a;i<b;i+=c)
#define ff first
#define ss second
#define pb push_back
#define pf push_front
#define ppb pop_back
#define ppf pop_front
#define be begin
#define rbe rbegin
#define all(a) a.be(),a.end()
#define lb(a,x) lower_bound(all(a),x)-a.be()
#define nl cout<<"\n";
#define ub(a,x) upper_bound(all(a),x)-a.be()
#define me max_element
#define mpl map<ll,ll>
#define umpl unordered_map<ll,ll>
#define stl stack<ll>
#define qul queue<ll>
#define sz(a) a.size()
#define rev(a) reverse(a.be(),a.end())
#define zbit(x) __builtin_ctzll(x)
#define sbit(x)  __builtin_popcountll(x)
#define lzbit(x) __builtin_clzll(x)
#define sl set<ll>
#define py cout<<"YES";
#define pm cout<<"-1";
#define pn cout<<"NO";
#define fbo find_by_order
#define ook order_of_key
#define pnt(x) cout<<x
#pragma GCC target("popcnt")

using namespace std;
using u64 = uint64_t;
using u128 = __uint128_t;
using namespace __gnu_pbds;


const ll hashp=1e18+7; //790738119649411319;
const ll mod=1e9+7; //998244353;
const ld pi= 3.141592653589793238;
const ll inf=2e18;


mt19937_64 rng(chrono::steady_clock::now().time_since_epoch().count());
 

template<typename T> 
using oset= tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update>;

u64 binpower(u64 base, u64 e, u64 mod) {
    u64 result = 1;
    base %= mod;
    while (e) {
        if (e & 1)
            result = (u128)result * base % mod;
        base = (u128)base * base % mod;
        e >>= 1;
    }
    return result;
}

bool check_composite(u64 n, u64 a, u64 d, int s) {
    u64 x = binpower(a, d, n);
    if (x == 1 || x == n - 1)
        return false;
    for (int r = 1; r < s; r++) {
        x = (u128)x * x % n;
        if (x == n - 1)
            return false;
    }
    return true;
};
bool iPrime(u64 n) { 
    if (n < 2)
        return false;

    int r = 0;
    u64 d = n - 1;
    while ((d & 1) == 0) {
        d >>= 1;
        r++;
    }

    for (int a : {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37}) {
        if (n == a)
            return true;
        if (check_composite(n, a, d, r))
            return false;
    }
    return true;
}
ll ext_gcd(ll a, ll b, ll &x, ll &y);


/*------------------------------------------------------------------------------------------------------------------------------------------------------------------*/
ll sm(vl a,ll s=0){for(auto i:a) s+=i;return s;}
void pre(vl &a){rep(i,1,sz(a)) a[i]+=a[i-1];}
void sieve(vb &x,ll n){x[0]=x[1]=0;for(ll i=2;i*i<=n;i++)if(x[i])for(ll j=i*i;j<=n;j+=i)x[j]=0;}
ll isprime(ll n){if(n==1||n==0)return 0;if(n==2||n==3)return 1;if(n%2==0||n%3==0)return 0;for(ll i=5;i<=n/2;i+=6)if(n%i==0||n%(i+2)==0)return 0;return 1;}
void primef(ll n,vl &x){if(!(n&1)){x.pb(2);while(!(n&1))n=n>>1;}for(ll i=3;i*i<=n;i+=2){if(n%i==0){x.pb(i);while(n%i==0)n/=i;}}if(n>2)x.pb(n);}
ll freq(ll n,ll d){if(n%d!=0)return 0;return 1+freq(n/d,d);}
ll lcm(ll a,ll b){ll x,y; return (a*b)/ext_gcd(a,b,x,y);}
void pow2(vl &x){x.pb(1);while(sz(x)<=60)x.pb(2*x[sz(x)-1]);}
bool sorta( pll a, pll b){return (a.ss < b.ss);}
bool sortd( pll a, pll b){return (a.ss > b.ss);}
void tobin(ll n,string &s){while(n>0){if(n&1)s.pb('1');else s.pb('0');n=n>>1;}}
void printv(vl v){for(auto i: v)cout<<i<<" ";}
char toc(ll n){char c='0';c+=n;return c;}
ll toi(char c){ll x=c-'0';return x;}
ll ain(char c){ll in=c-'a';return in;}
ll mi(ll a,ll b){return a+(b-a)/2;} 
/*------------------------------------------------------------------------------------------------------------------------------------------------------------------*/

//TODO: Import your classes over here\\





/*------------------------------------------------------------------------------------------------------------------------------------------------------------------*/
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/*------------------------------------------------------------------------------------------------------------------------------------------------------------------*/

ll ext_gcd(ll a, ll b, ll &x, ll &y)
{
    if(!b)
    {
        x=1,y=0;
        return a;
    }
    ll x1,y1;
    ll g=ext_gcd(b,a%b,x1,y1);
    x=y1,y=x1-(a/b)*y1;
    return g;
}
ll powe(ll a,ll p,ll m=inf)
{
    if(p==0)
    return 1;
    ll result=powe(a,p>>1,m);
    if(p&1)
    return ((((a%m)*result)%m)*result)%m;
    return (result*result)%m;
}
ll add(ll a,ll b)
{
    return ((a%mod)+(b%mod))%mod;
}
ll mul(ll a,ll b)
{
    return ((a%mod)*(b%mod))%mod;
}
ll sub(ll a,ll b)
{
    return ((a%mod)-(b%mod)+mod)%mod;
}
ll divi(ll a,ll b)
{
    b=powe(b,mod-2,mod);
    return mul(a,b);
}
void facto(vl &f, ll n)
{
    f[0]=1,f[1]=1;
    rep(i,2,n)
    f[i]=mul(i,f[i-1]);
    return;
}


// Solves a1X + b1Y = c1, a2X + b2Y = c2; 
pll linearEquation2Var(ll a1, ll b1, ll c1, ll a2, ll b2, ll c2){
    ll xx=c1*a2;
    ll yy=c2*a1;
    
    xx-=yy;
    
    ll bb=b1*a2-b2*a1;
    
    if(xx%bb)return {-1,-1};
    
    ll Y=xx/bb;
    
    ll zz=c1-b1*Y;
    if(zz%a1)return {-1,-1};
    
    ll X=zz/a1;
    
    return {X,Y};
    
}


/*------------------------------------------------------------------------------------------------------------------------------------------------------------------*/
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/*------------------------------------------------------------------------------------------------------------------------------------------------------------------*/

class DSU {
    public:
    
    vector<ll> parent, length;
    DSU(ll n){
        vector<ll> temp(n,1);
        length=temp;
        parent=temp;
        for(int i=0;i<n;i++)
            parent[i]=i;
    }

    ll findParent(ll x){
        if(parent[x]==x)return x;
        return parent[x]=findParent(parent[x]);
    }

    bool joinNodes(ll x, ll y){
        x=findParent(x);
        y=findParent(y);

        if(x==y)return false;
        
        if(length[y]>length[x]){
            length[y]+=length[x];
            parent[x]=y;
        }
        else{
            length[x]+=length[y];
            parent[y]=x;
        }
        
        return true;
    }
    
    
};

struct X{
    ll l,val,r;
};


bool comp(X a, X b){
    if(a.l==b.l)return a.r<b.r;
    return a.l<b.l;
}
void solve()
{

    // TAKE BREAKS
    // THINK OF ALTERNATE APPROACHES 
    // DP, Greedy, Sqrt Decomposition, DSU, Djikstra, Binary Search
    // Two Pointers, Hashing, Stars and Bars, Two Pointers, Derangements
    // Euler Tour, Segment Tree, LCA, Binary Lifting
    // Try to write down and analyze patterns
    
    //**PRASOON**\\

    ll n,k,c,l,r,m,p,q,t;
    cin>>n>>k;
    ll ans=k;
    
    vector<X> a(n);
    
    rep(i,0,n){
        cin>>a[i].l>>a[i].r>>a[i].val;
    }
    
    sort(all(a), comp);
    
    // for(auto i: a)cout<<i.l<<" "<<i.r<<" "<<i.val<<"   ";
    
    for(auto cur: a){
        if(cur.l<=ans && cur.r>=ans){
            ans=max(ans, cur.val);
        }
    }
    
    pnt(ans);
    
    
    return;
}



int main() 
{
    ios_base::sync_with_stdio(false);
    cin.tie(NULL);
    cout.tie(NULL);
    srand(time(NULL));
    //cout<<fixed<<setprecision(9);
    ll t;
    cin>>t;
    
    while(t--)
    {
        solve();
        nl 
    }
    

    return 0;
}
