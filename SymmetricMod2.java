import java.math.BigInteger;
import java.util.*;
public class SymmetricMod2 {
    private static long usedMem() {
        Runtime r=Runtime.getRuntime();
        return r.totalMemory()-r.freeMemory();
    }
    private static String memStats() {
        return String.format("(tot=%d,used=%d)",Runtime.getRuntime().totalMemory(),usedMem());
    }
    private static int[] toArr(List<Integer> L) {
        int[] A=new int[L.size()];
        for (int i=0; i<A.length; i++) A[i]=L.get(i);
        return A;
    }
    private static BigInteger nCr(int n, int k) {
        if (n<k) return BigInteger.ZERO;
        BigInteger out=BigInteger.ONE;
        for (int i=n; i>n-k; i--) out=out.multiply(new BigInteger(i+""));
        for (int i=1; i<=k; i++) out=out.divide(new BigInteger(i+""));
        return out;
    }

    //matrix A is stored as number b s.t. A[i][j]=i*N+j -th bit of b
    //tensor T is stored as array t s.t. T[i][j][k]=k -th bit of t[i*N2+j]
    private static int N, N2, N4, N6;
    private static int MASK;
    private static int NPERMS, MAJOR_GROUP_SIZE;
    private static int[][] permutedMats;
    //over mod 2, a+b =a bitwise_xor b =a^b and a*b =a bitwise_and b =a&b
    private static int[] xor(int[] A, int[] B) {
        if (A.length!=B.length) throw new RuntimeException();
        int[] C=new int[A.length];
        for (int i=0; i<A.length; i++) C[i]=A[i]^B[i];
        return C;
    }
    private static int[] xortensor(int[] triplets) {
        int[] out=new int[N4];
        for (int tri:triplets) {
            int A=tri&MASK, B=(tri>>N2)&MASK, C=(tri>>(2*N2))&MASK;
            for (int i=0; i<N2; i++) if (((A>>i)&1)==1)
                for (int j=0; j<N2; j++) if (((B>>j)&1)==1)
                    out[i*N2+j]^=C;
        }
        return out;
    }

    private static int[] transformedTris(int xc, int yc, int zc) {
        int[] out=new int[MAJOR_GROUP_SIZE]; int i=0;
        for (int[] F:permutedMats) for (int[] tri:new int[][] {{xc,yc,zc},{yc,zc,xc},{zc,xc,yc}})
            out[i++]=F[tri[0]]|(F[tri[1]]<<N2)|(F[tri[2]]<<(2*N2));
        return out;
    }

    private static int G, Gd32;
    private static int[][] compressionClasses;
    private static int[] symmCompress(int[] T) {
        int[] out=new int[Gd32];
        for (int g=0; g<G; g++) {
            int[] group=compressionClasses[g];
            int v=(T[group[0]/N2]>>(group[0]%N2))&1;
            for (int i:group) if (v!=((T[i/N2]>>(i%N2))&1)) throw new RuntimeException("Tensor not symmetric enough for compression.");
            out[g>>>5]|=((long)v)<<(g&31);
        }
        return out;
    }
    public static int compareTensors(int[] t0, int[] t1) {
        for (int i=t0.length-1; i>0; i--) if (t0[i]!=t1[i]) return Integer.compare(t0[i],t1[i]);
        return Integer.compare(t0[0],t1[0]);
    }
    private abstract static class MergerByTensor {
        abstract int[] tensor(int e);
        public int[] mergedElems(List<Integer> E, Comparator<Integer> comp) {
            //long st=System.currentTimeMillis();
            E.sort(new Comparator<Integer>() {
                public int compare(Integer o1, Integer o2) {
                    int d=compareTensors(tensor(o1),tensor(o2));
                    return d==0?(comp==null?Integer.compare(o1,o2):comp.compare(o1,o2)):d;
                }
            });
            //System.out.println("sort time="+(System.currentTimeMillis()-st)+" m="+memStats());

            //st=System.currentTimeMillis();
            int[] tmp=new int[E.size()]; int n=0;
            for (int i=0; i<E.size();) {
                tmp[n++]=E.get(i);
                int j=i; while (j<E.size() && compareTensors(tensor(E.get(i)),tensor(E.get(j)))==0) j++;
                i=j;
            }
            //System.out.println("remove duplicates time="+(System.currentTimeMillis()-st)+" m="+memStats());
            //System.out.println("cnt remaining="+n);
            return Arrays.copyOf(tmp,n);
        }
    }
    private abstract static class TensorSet {
        //stores a range of integers [0,R), where each integer e has an implicit associated array key(e)
        //when querying for a specific key: if key does not exist, return -1
        abstract int[] set_tensor(int e);
        long searches, binSearches, binWork;
        long[] filterWork;
        private long[][] filters;
        //works even though int is signed, because >>> will rotate the signed bit
        private void add(long[] filter, int v) {
            filter[v>>>6]|=1L<<(v&63);
        }
        private long bit(long[] filter, int v) {
            return filter[v>>>6]&(1L<<(v&63));
        }
        //TODO: TRY OPEN ADDRESSING
        private int H=100_000_007;
        private int[][] chains;
        private int hash(int[] key) {
            int out=0;
            for (int v:key) out=out*31+v;
            return ((out%H)+H)%H;
        }
        public TensorSet(int range, Comparator<Integer> comp) {
            long st=System.currentTimeMillis();
            List<List<Integer>> bins=new ArrayList<>();
            for (int h=0; h<H; h++) bins.add(null);
            for (int e=0; e<range; e++) {
                int h=hash(set_tensor(e));
                if (bins.get(h)==null) bins.set(h,new ArrayList<>());
                bins.get(h).add(e);
            }
            System.out.println("hash binning time="+(System.currentTimeMillis()-st)+" m="+memStats());

            st=System.currentTimeMillis();
            chains=new int[H][];
            for (int h=0; h<H; h++) {
                List<Integer> bin=bins.get(h);
                if (bin!=null)
                    chains[h]=new MergerByTensor() {
                        int[] tensor(int e) { return set_tensor(e); }
                    }.mergedElems(bin,comp);
            }
            System.out.println("element merging time="+(System.currentTimeMillis()-st)+" m="+memStats());

            st=System.currentTimeMillis();
            filters=new long[Gd32][1<<26];
            filterWork=new long[Gd32];
            for (int[] ch:chains) if (ch!=null) for (int e:ch) {
                int[] K=set_tensor(e);
                for (int f = 0; f< Gd32; f++) add(filters[f],K[f]);
            }
            System.out.println("bitset filter time="+(System.currentTimeMillis()-st)+" m="+memStats());
            int max=0, cnt=0, tot=0;
            for (int[] chain:chains) if (chain!=null) { max=Math.max(max,chain.length); cnt++; tot+=chain.length; }
            System.out.println("max chain length="+max+", # chains="+cnt);
            System.out.println("cnt remaining="+tot);
        }
        private int binsearch(int[] elems, int[] K) {
            if (elems==null) return -1;
            binSearches++;
            int lo=0, hi=elems.length-1;
            while (lo<hi) {
                binWork++;
                int mi=(lo+hi)/2;
                if (compareTensors(K,set_tensor(elems[mi]))<=0) hi=mi;
                else lo=mi+1;
            }
            return compareTensors(K,set_tensor(elems[lo]))==0?elems[lo]:-1;
        }
        public int getXorOf(int[] Ka, int[] Kb) {
            searches++;
            for (int f = 0; f< Gd32; f++) {
                filterWork[f]++;
                if (bit(filters[f],Ka[f]^Kb[f])==0) return -1;
            }
            int[] K=xor(Ka,Kb);
            return binsearch(chains[hash(K)],K);
        }
    }

    private static void checkProduct(List<int[]> T, List<int[]> L, List<int[]> R) {
        Set<String> prod=new HashSet<>();
        for (int[] l:L) for (int[] r:R) {
            int[] p=new int[l.length];
            for (int i=0; i<l.length; i++) p[i]=l[i]+r[i];
            prod.add(Arrays.toString(p));
        }
        for (int[] p:T) if (!prod.contains(Arrays.toString(p))) throw new RuntimeException("Product does not superset target.");
    }

    public static void main(String[] args) {
        System.out.println("max heap size="+Runtime.getRuntime().maxMemory());
        System.out.println("m="+memStats());

        N=3;
        N2=N*N; N4=N2*N2; N6=N4*N2;

        int MAX_Rm=5, MAX_SM=2, MAX_Zm=729, MAX_ZM=729;
        BigInteger MEM_LIMIT=new BigInteger(""+200_000_000);
        int DFS_TIME_LIMIT=100_000;
        String MODE="SHIFT";
        System.out.printf("N=%d MAX_Rm=%d MAX_SM=%d MAX_Zm=%d MAX_ZM=%d MODE=%s%n",N,MAX_Rm,MAX_SM,MAX_Zm,MAX_ZM,MODE);
        System.out.printf("MEM_LIMIT=%d DFS_TIME_LIMIT=%d%n",MEM_LIMIT,DFS_TIME_LIMIT);

        int[] TARGET=new int[N6];
        for (int i=0; i<N; i++) for (int j=0; j<N; j++) for (int k=0; k<N; k++)
            TARGET[(i*N+j)*N2+(j*N+k)]|=1<<(k*N+i);
        MASK=(1<<N2)-1;

        //generate the set of transformation functions that will be used to enforce symmetry
        {
            List<int[]> perms;
            switch (MODE) {
                case "FLIP":
                    perms=new ArrayList<>();
                    for (int t=0; t<2; t++) {
                        int[] p=new int[N]; for (int i=0; i<N; i++) p[i]=t==0?i:(N-1-i);
                        perms.add(p);
                    }
                    break;
                case "SHIFT":
                    perms=new ArrayList<>();
                    for (int s=0; s<N; s++) {
                        int[] p=new int[N]; for (int i=0; i<N; i++) p[i]=(i+s)%N;
                        perms.add(p);
                    }
                    break;
                case "S3":
                    perms=new ArrayList<>(Collections.singletonList(new int[] {0}));
                    for (int n=2; n<=N; n++) {
                        List<int[]> tmp=new ArrayList<>();
                        for (int[] p:perms)
                            for (int i=0; i<n; i++) {
                                int[] np=new int[n];
                                System.arraycopy(p,0,np,0,i);
                                np[i]=n-1;
                                System.arraycopy(p,i,np,i+1,n-1-i);
                                tmp.add(np);
                            }
                        perms=tmp;
                    }
                    break;
                default:
                    throw new RuntimeException("Symmetry type not found.");
            }
            NPERMS=perms.size();
            permutedMats=new int[NPERMS][1<<N2];
            for (int b=1; b<(1<<N2); b++)
                for (int pi=0; pi<NPERMS; pi++) {
                    int[] p=perms.get(pi);
                    int nb=0;
                    for (int r=0; r<N; r++) for (int c=0; c<N; c++) nb|=((b>> (p[r]*N+p[c]) )&1) << (r*N+c);
                    permutedMats[pi][b]=nb;
                }
        }
        MAJOR_GROUP_SIZE=3*NPERMS;
        int MAXRANK=MAX_Rm+MAJOR_GROUP_SIZE*MAX_SM;
        System.out.println("MAJOR_GROUP_SIZE="+MAJOR_GROUP_SIZE+" MAXRANK="+MAXRANK);

        //create the index groups used for tensor compression
        {
            int[] compressionClassNum=new int[N6]; Arrays.fill(compressionClassNum,-1); G=0; {
            int[] log2=new int[1<<N2]; for (int i=0; i<N2; i++) log2[1<<i]=i;
            for (int i=0; i<N2; i++) for (int j=0; j<N2; j++) for (int k=0; k<N2; k++) if (compressionClassNum[i*N4+j*N2+k]==-1) {
                for (int tric:transformedTris(1<<i,1<<j,1<<k))
                    compressionClassNum[log2[tric&MASK]*N4+log2[(tric>>N2)&MASK]*N2+log2[(tric>>(2*N2))&MASK]]=G;
                G++;
            }
        }
            Gd32 =(G-1)/32+1;
            System.out.println("G="+G+" F="+ Gd32);
            int[] compressionClassSizes=new int[G];
            for (int i=0; i<N6; i++) compressionClassSizes[compressionClassNum[i]]++;
            compressionClasses=new int[G][]; {
            for (int g=0; g<G; g++) compressionClasses[g]=new int[compressionClassSizes[g]];
            int[] tmp=new int[G];
            for (int i=0; i<N6; i++) {
                int g=compressionClassNum[i];
                compressionClasses[g][tmp[g]++]=i;
            }
        }
            System.out.println("# bits in compressed tensor="+G);
        }

        //enumerate the resulting tensor of all sparse groups generated from a single matrix triplet
        int[][] groupTensor=new int[1<<(3*N2)][];
        int[] groupSize=new int[1<<(3*N2)];
        int[][] triplets=new int[MAJOR_GROUP_SIZE+1][]; {
            System.out.println("generating groups");
            int[] bitcnt=new int[1<<N2]; bitcnt[0]=0; for (int i=1; i<(1<<N2); i++) bitcnt[i]=bitcnt[i/2]+i%2;
            int[] groupSzHist=new int[MAJOR_GROUP_SIZE+1];
            boolean[] taken=new boolean[1<<(3*N2)];
            List<List<Integer>> tris=new ArrayList<>();
            for (int r=0; r<=MAJOR_GROUP_SIZE; r++) tris.add(new ArrayList<>());
            long st=System.currentTimeMillis(), mark=0, work=0;
            for (int a=1; a<(1<<N2); a++) for (int b=1; b<(1<<N2); b++) for (int c=1; c<(1<<N2); c++) {
                int triplet=a|(b<<N2)|(c<<(2*N2));
                if (!taken[triplet]) {
                    long time=System.currentTimeMillis()-st;
                    if (time>=mark) {
                        mark+=10_000;
                        System.out.printf("work=%d t=%d m=%s histogram of sizes=%s%n",
                                work,time,memStats(),Arrays.toString(groupSzHist));
                    }
                    int[] triGroup=new int[MAJOR_GROUP_SIZE];
                    int S=0;
                    for (int ntri:transformedTris(a,b,c))
                        if (!taken[ntri]) {
                            taken[ntri]=true;
                            triGroup[S++]=ntri;
                        }
                    triGroup=Arrays.copyOf(triGroup,S);
                    boolean major=S==MAJOR_GROUP_SIZE;
                    if (bitcnt[a]*bitcnt[b]*bitcnt[c]<=(major?MAX_ZM:MAX_Zm)) {
                        groupSzHist[S]++;
                        groupSize[triplet]=S;
                        int[] eval=symmCompress(xortensor(triGroup));
                        groupTensor[triplet]=eval;
                        tris.get(S).add(triplet);
                    }
                    work++;
                }
            }
            System.out.printf("work=%d t=%d m=%s histogram of sizes=%s end%n",
                    work,System.currentTimeMillis()-st,memStats(),Arrays.toString(groupSzHist));
            for (int r=0; r<=MAJOR_GROUP_SIZE; r++)
                triplets[r]=new MergerByTensor() {
                    int[] tensor(int tri) { return groupTensor[tri]; }
                }.mergedElems(tris.get(r),null);
        }
        System.out.println("m="+memStats());


        int[] triCnts=new int[MAJOR_GROUP_SIZE+1];
        for (int r=0; r<=MAJOR_GROUP_SIZE; r++) triCnts[r]=triplets[r].length;
        System.out.println(Arrays.toString(triCnts));

        class Profiles {
            static List<int[]> out;
            static int[] limits;
            static int[] freq;
            static int maxTot;
            static void dfs(int rank, int m) {
                if (m==0) {
                    out.add(Arrays.copyOf(freq,freq.length));
                    return;
                }
                for (int cnt=0; rank-cnt*m>=0 && cnt<=limits[m]; cnt++) {
                    freq[m]=cnt;
                    dfs(rank-cnt*m,m-1);
                }
            }
            static List<int[]> generate(int maxTot, int[] limits) {
                Profiles.maxTot=maxTot; Profiles.limits=limits;
                out=new ArrayList<>();
                freq=new int[limits.length];
                dfs(maxTot,limits.length-1);
                return out;
            }
        }

        class ProfileHelp {
            static BigInteger profileCost(int[] p, int[] triCnts) {
                BigInteger n=BigInteger.ONE;
                for (int r=1; r<=MAJOR_GROUP_SIZE; r++) n=n.multiply(nCr(triCnts[r],p[r]));
                return n;
            }
            static int[][] sumTable(List<int[]> P) {
                int sz=P.size();
                int[][] out=new int[sz][sz];
                Map<String,Integer> profile2id=new HashMap<>();
                for (int pi=0; pi<sz; pi++) profile2id.put(Arrays.toString(P.get(pi)),pi);
                for (int pi=0; pi<sz; pi++) for (int pj=0; pj<sz; pj++) {
                    int[] a=new int[MAJOR_GROUP_SIZE+1];
                    for (int r=0; r<=MAJOR_GROUP_SIZE; r++) a[r]=P.get(pi)[r]+P.get(pj)[r];
                    out[pi][pj]=profile2id.getOrDefault(Arrays.toString(a),-1);
                }
                return out;
            }
        }
        List<int[]> profiles=new ArrayList<>(); {
            int[] minor_triCnts=Arrays.copyOf(triCnts,MAJOR_GROUP_SIZE+1);
            minor_triCnts[MAJOR_GROUP_SIZE]=0;
            for (int[] pmin:Profiles.generate(MAX_Rm,minor_triCnts))
                for (int s=0; s<=MAX_SM; s++) {
                    int[] p=Arrays.copyOf(pmin,MAJOR_GROUP_SIZE+1);
                    p[MAJOR_GROUP_SIZE]=s;
                    profiles.add(p);
                }
            System.out.println("profiles");
            //for (int[] p:profiles) System.out.println(Arrays.toString(p));
        }
        int nP=profiles.size();
        System.out.println("# profiles="+nP);

        int[][] table=ProfileHelp.sumTable(profiles);
        //System.out.println("table"); for (int[] r:table) { for (int v:r) System.out.printf(" %2s",v==-1?".":v); System.out.println(); }

        { //calculate theoretical optimal score
            BigInteger all=BigInteger.ZERO;
            for (int[] p:profiles) all=all.add(ProfileHelp.profileCost(p,triCnts));
            BigInteger arg=(all.sqrt()).min(MEM_LIMIT);
            System.out.println("theoretical lowest score="+(arg.add(all.divide(arg))));
        }
        class TableDFS {
            BigInteger[] rowCost, clmCost;
            //[n] denotes the set {0,...n-1}
            //given n x m matrix A, A[i][j] \in [k],
            //find R \in [n], C \in [m], s.t. {A[r][c] | r \in R, c \in C} \supseteq [k]
            int n, m, k;
            List<List<Integer>> locs;
            boolean[] rowTaken, clmTaken;
            boolean[][] bsol; BigInteger bscr; BigInteger[] bcostInfo;
            long st, mark, work;
            private void dfs(int v, BigInteger totRowCost, BigInteger totClmCost) {
                long time=System.currentTimeMillis()-st;
                if (time>=mark) {
                    mark+=10_000;
                    System.out.printf("work=%d bscr=%d t=%d%n",work,bscr,time);
                }
                if (time>=DFS_TIME_LIMIT) return;
                if (totRowCost.compareTo(MEM_LIMIT)>0) return;
                work++;
                BigInteger scr=totRowCost.add(totClmCost);
                if (v==k) {
                    if (bscr==null || scr.compareTo(bscr)<0) {
                        bscr=scr;
                        bsol=new boolean[][] {Arrays.copyOf(rowTaken,n),Arrays.copyOf(clmTaken,m)};
                        bcostInfo=new BigInteger[] {totRowCost,totClmCost};
                    }
                    return;
                }
                for (int loc:locs.get(v)) if (rowTaken[loc/m] && clmTaken[loc%m]) {
                    dfs(v+1,totRowCost,totClmCost);
                    return;
                }
                BigInteger[] dscr=new BigInteger[n*m];
                List<Integer> sortedLocs=new ArrayList<>(locs.get(v));
                for (int loc:sortedLocs) {
                    int r=loc/m, c=loc%m;
                    dscr[loc]=(rowTaken[r]?BigInteger.ZERO:rowCost[r]).add(clmTaken[c]?BigInteger.ZERO:clmCost[c]);
                }
                sortedLocs.sort(new Comparator<Integer>() {
                    public int compare(Integer o1, Integer o2) {
                        return dscr[o1].compareTo(dscr[o2]);
                    }
                });
                for (int loc:sortedLocs) {
                    if (bscr!=null && (scr.add(dscr[loc])).compareTo(bscr)>=0) break;
                    int r=loc/m, c=loc%m;
                    boolean r0=rowTaken[r], c0=clmTaken[c];
                    rowTaken[r]=true; clmTaken[c]=true;
                    dfs(v+1,totRowCost.add(r0?BigInteger.ZERO:rowCost[r]),totClmCost.add(c0?BigInteger.ZERO:clmCost[c]));
                    rowTaken[r]=r0; clmTaken[c]=c0;
                }
            }
            public TableDFS(int[][] table, BigInteger[] rowCost, BigInteger[] clmCost, int k) {
                st=System.currentTimeMillis(); mark=0; work=0;
                this.rowCost=rowCost; this.clmCost=clmCost;
                n=table.length; m=table[0].length; this.k=k;
                locs=new ArrayList<>();
                for (int v=0; v<k; v++) locs.add(new ArrayList<>());
                for (int i=0; i<n; i++) for (int j=0; j<m; j++) {
                    int v=table[i][j];
                    if (v>-1) locs.get(v).add(i*m+j);
                }
                rowTaken=new boolean[n]; clmTaken=new boolean[m];
                bsol=null; bscr=null; bcostInfo=null;
                dfs(0,BigInteger.ZERO,BigInteger.ZERO);
                System.out.printf("work=%d bscr=%d t=%d%n",work,bscr,System.currentTimeMillis()-st);
            }
        }

        List<int[]> P0=new ArrayList<>(), P1=new ArrayList<>(); {
            BigInteger[] rowCost=new BigInteger[nP];
            for (int pi=0; pi<nP; pi++) rowCost[pi]=ProfileHelp.profileCost(profiles.get(pi),triCnts);
            TableDFS info=new TableDFS(table,rowCost,rowCost,nP);
            boolean[][] bdivide=info.bsol;
            System.out.println("expected costs="+Arrays.toString(info.bcostInfo));
            for (int pi=0; pi<nP; pi++) if (bdivide[0][pi]) P0.add(profiles.get(pi));
            for (int pi=0; pi<nP; pi++) if (bdivide[1][pi]) P1.add(profiles.get(pi));
            checkProduct(profiles,P0,P1);
            System.out.print("map "); for (int[] p:P0) System.out.print(" "+Arrays.toString(p)); System.out.println();
            System.out.print("iter"); for (int[] p:P1) System.out.print(" "+Arrays.toString(p)); System.out.println();
        }

        abstract class ForEachSetOfProfile {
            int[] profile, idxs, tris;
            abstract void process(int[] tris, int[] tensor);
            private void iter(int r, int imin, int combolen, int trii, int[] tensor) {
                if (r==profile.length) process(tris,tensor);
                else if (combolen==profile[r]) iter(r+1,0,0,trii,tensor);
                else {
                    for (int i=imin; i<triCnts[r]; i++) {
                        int tri=triplets[r][i];
                        idxs[trii]=i;
                        tris[trii]=tri;
                        int[] ntensor=xor(tensor,groupTensor[tri]);
                        iter(r,i+1,combolen+1,trii+1,ntensor);
                    }
                }
            }
            public ForEachSetOfProfile(int[] P) {
                profile=P;
                int tot=0; for (int r=1; r<P.length; r++) tot+=P[r];
                idxs=new int[tot]; tris=new int[tot];
                iter(1,0,0,0,new int[Gd32]);
            }
        }
        class Combo2Tris {
            int totrank(int[] tris) {
                int out=0;
                for (int tri:tris) out+=groupSize[tri];
                return out;
            }
            int[] tris2tensor(int[] tris) {
                int[] tensor=new int[Gd32];
                for (int tri:tris) tensor=xor(tensor,groupTensor[tri]);
                return tensor;
            }
        } Combo2Tris $=new Combo2Tris();

        TensorSet D0; List<int[]> triss0=new ArrayList<>(); {
            long st=System.currentTimeMillis();
            final long[] mark={0};
            for (int[] p:P0)
                new ForEachSetOfProfile(p) {
                    void process(int[] tris, int[] tensor) {
                        long time=System.currentTimeMillis()-st;
                        if (time>=mark[0]) {
                            mark[0]+=10_000;
                            System.out.printf("sz=%d t=%d%n",triss0.size(),time);
                        }
                        triss0.add(Arrays.copyOf(tris,tris.length));
                    }
                };
            System.out.printf("sz=%d t=%d m=%s%n",triss0.size(),System.currentTimeMillis()-st,memStats());
            D0=new TensorSet(triss0.size(), new Comparator<Integer>() {
                @Override
                public int compare(Integer o1, Integer o2) {
                    return $.totrank(triss0.get(o1))-$.totrank(triss0.get(o2));
                }
            }) {
                int[] set_tensor(int e) {
                    return $.tris2tensor(triss0.get(e));
                }
            };
        }
        System.out.println("searching m="+memStats());
        long st=System.currentTimeMillis();
        final long[] mark={0}, searches0={0};
        final int[] brank={Integer.MAX_VALUE};
        BigInteger tot; {
            BigInteger tmp=BigInteger.ZERO; for (int[] p:P1) tmp=tmp.add(ProfileHelp.profileCost(p,triCnts));
            tot=tmp;
        }
        String statsString="%3f%% %3f%% searches=%d filterWork=%s binSearches=%d binWork=%d t=%d m=%s%n";
        int[] CTARGET=symmCompress(TARGET);
        for (int pi=0; pi<P1.size(); pi++) {
            int[] p1=P1.get(pi);
            D0.searches=0; Arrays.fill(D0.filterWork,0); D0.binSearches=0; D0.binWork=0;
            BigInteger p1tot=ProfileHelp.profileCost(p1,triCnts);
            System.out.printf("%d/%d %s expected # searches=%d%n",pi,P1.size(),Arrays.toString(p1),p1tot);
            //TODO: ITERATE FOR-LOOP FOR LAST MATRIX TRIPLET
            int firstRank; {
                int tmp=-1;
                for (int r=0; r<=MAJOR_GROUP_SIZE; r++) if (p1[r]>0) { tmp=r; break; }
                firstRank=tmp;
            }
            if (firstRank==-1) {
                int e=D0.getXorOf(CTARGET,new int[Gd32]);
                if (e>=0) {
                    int[] tris0=triss0.get(e);
                    int rank=$.totrank(tris0);
                    if (rank<brank[0]) {
                        brank[0]=rank;
                        System.out.println("rank="+rank+" generated from");
                        for (int[] combo:new int[][] {tris0})
                            for (int tri:combo) {
                                StringBuilder s=new StringBuilder();
                                for (int m:new int[] {tri&MASK,(tri>>N2)&MASK,(tri>>(2*N2))&MASK}) {
                                    int[] A=new int[N2]; for (int i=0; i<N2; i++) A[i]=(m>>i)&1;
                                    s.append(Arrays.toString(A)).append(",");
                                }
                                System.out.println(s.substring(0,s.length()-1));
                            }
                    }
                }
            }
            else {
                int[] subp1=Arrays.copyOf(p1,MAJOR_GROUP_SIZE+1);
                subp1[firstRank]--;
                System.out.println("sub="+Arrays.toString(subp1));
                new ForEachSetOfProfile(subp1) {
                    void process(int[] stris1, int[] stensor1) {
                        long time=System.currentTimeMillis()-st;
                        if (time>=mark[0]) {
                            mark[0]+=10_000;
                            System.out.printf(statsString,(D0.searches+searches0[0])/tot.doubleValue()*100,D0.searches/p1tot.doubleValue()*100,
                                    D0.searches,Arrays.toString(D0.filterWork),D0.binSearches,D0.binWork,time,memStats());
                        }
                        if (!Arrays.equals($.tris2tensor(stris1),stensor1)) throw new RuntimeException();
                        int[] tmptensor=xor(CTARGET,stensor1);
                        for (int idx=0; idx<(idxs.length==0 || subp1[firstRank]==0?triplets[firstRank].length:idxs[0]); idx++) {
                            int firstTri=triplets[firstRank][idx];
                            int e=D0.getXorOf(tmptensor,groupTensor[firstTri]);
                            if (e>=0) {
                                int[] tris0=triss0.get(e), tris1=Arrays.copyOf(stris1,stris1.length+1);
                                tris1[stris1.length]=firstTri;
                                int rank=$.totrank(tris0)+$.totrank(tris1);
                                if (rank<brank[0]) {
                                    brank[0]=rank;
                                    System.out.println("rank="+rank+" generated from");
                                    for (int[] combo:new int[][] {tris0,tris1})
                                        for (int tri:combo) {
                                            StringBuilder s=new StringBuilder();
                                            for (int m:new int[] {tri&MASK,(tri>>N2)&MASK,(tri>>(2*N2))&MASK}) {
                                                int[] A=new int[N2]; for (int i=0; i<N2; i++) A[i]=(m>>i)&1;
                                                s.append(Arrays.toString(A)).append(",");
                                            }
                                            System.out.println(s.substring(0,s.length()-1));
                                        }
                                }
                            }
                        }
                    }
                };
            }
            System.out.printf(statsString,(D0.searches+searches0[0])/tot.doubleValue()*100,D0.searches/p1tot.doubleValue()*100,
                    D0.searches,Arrays.toString(D0.filterWork),D0.binSearches,D0.binWork,System.currentTimeMillis()-st,memStats());
            searches0[0]+=D0.searches;
        }
    }
}
