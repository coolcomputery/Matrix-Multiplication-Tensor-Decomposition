import java.util.*;
public class SymmetricMod2 {
    private static long usedMem() {
        Runtime r=Runtime.getRuntime();
        return r.totalMemory()-r.freeMemory();
    }
    private static String memStats() {
        return String.format("(tot=%d,used=%d)",Runtime.getRuntime().totalMemory(),usedMem());
    }

    //matrix A is stored as number b s.t. A[i][j]=i*N+j -th bit of b
    //tensor T is stored as array t s.t. T[i][j][k]=k -th bit of t[i*N2+j]
    private static int N, N2, N4, N6;
    private static int MASK;
    private static int NPERMS, MAJOR_GROUP_SIZE;
    private static int[][] permutedMats;
    //over mod 2, a+b = a bitwise_xor b = a^b and a*b = a bitwise_and b = a&b
    private static long[] xor(long[] A, long[] B) {
        if (A.length!=B.length) throw new RuntimeException();
        long[] C=new long[A.length];
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

    private static int G;
    private static int[][] compressionClasses;
    private static long[] symmCompress(int[] T) {
        long[] out=new long[(G-1)/64+1];
        for (int g=0; g<G; g++) {
            int[] group=compressionClasses[g];
            int v=(T[group[0]/N2]>>(group[0]%N2))&1;
            for (int i:group) if (v!=((T[i/N2]>>(i%N2))&1)) throw new RuntimeException("Tensor not symmetric enough for compression.");
            out[g>>>6]|=((long)v)<<(g&63);
        }
        return out;
    }

    //map long[] --> int[]
    //when querying key: if key does not exist, return -1
    private static class ArrMap {
        public static int compareKey(long[] a, long[] b) {
            //should be a valid comparison system even though long is signed typed
            for (int i=a.length-1; i>0; i--) if (a[i]!=b[i]) return Long.compare(a[i],b[i]);
            return Long.compare(a[0],b[0]);
        }
        private static class Pair implements Comparable<Pair> {
            final long[] key;
            final int[] val;
            public Pair(long[] k, int[] v) {
                key=k;
                val=v;
            }
            public int compareTo(Pair o) {
                return compareKey(key,o.key);
            }
        }
        int sz;
        List<Pair> pairsList; Pair[] pairs;
        boolean prepared=false;
        long searches, binSearches, binWork;
        long[] filterWork;
        //TODO: MULTIPLE FILTERS
        private long[][] filters;
        public final int filterPow=32;
        private final long filterMask=(1L<<filterPow)-1;
        public ArrMap() {
            pairsList=new ArrayList<>();
        }
        public void put(long[] A, int[] v) {
            if (prepared) throw new RuntimeException();
            pairsList.add(new Pair(A,v));
        }
        private long bithash(long[] K) {
            return K[0]&filterMask;
        }
        public void prepare(boolean advanced) {
            prepare(null,advanced);
        }
        public void prepare(Comparator<int[]> comp, boolean advanced) {
            if (prepared) return;
            long st=System.currentTimeMillis();
            pairsList.sort(new Comparator<Pair>() {
                public int compare(Pair o1, Pair o2) {
                    int k=compareKey(o1.key,o2.key);
                    return k==0?(comp==null?0:comp.compare(o1.val,o2.val)):k;
                }
            });
            System.out.println("sort time="+(System.currentTimeMillis()-st));

            st=System.currentTimeMillis();
            int n=0;
            for (int i=0; i<pairsList.size();) {
                long[] K=pairsList.get(i).key;
                int j=i;
                while (j< pairsList.size() && compareKey(K, pairsList.get(j).key)==0)
                    j++;
                pairsList.set(n++, pairsList.get(i));
                i=j;
            }
            for (int i=pairsList.size()-1; i>=n; i--) pairsList.remove(i);
            prepared=true;
            System.out.println("prep time="+(System.currentTimeMillis()-st));

            if (advanced) {
                st=System.currentTimeMillis();
                filters=new long[G/32+1][1<<(filterPow-6)];
                for (Pair p:pairsList)
                    for (int f=0; f<filters.length; f++) {
                        int v=(int)((p.key[f/2]>>(filterPow*(f%2)))&filterMask);
                        filters[f][v>>>6]|=1L<<(v&63);
                    }
                System.out.println("filter time="+(System.currentTimeMillis()-st));
                filterWork=new long[filters.length];
            }
            pairs=pairsList.toArray(new Pair[0]);

            sz=pairsList.size();
            pairsList=null;
        }
        private int[] binsearch(long[] K, Pair[] ps) {
            if (ps==null) return null;
            binSearches++;
            int lo=0, hi=ps.length-1;
            if (compareKey(K,ps[lo].key)<0
                    || compareKey(K,ps[hi].key)>0) return null;
            while (lo<hi) {
                binWork++;
                int mi=(lo+hi)/2;
                if (compareKey(K,ps[mi].key)<=0) hi=mi;
                else lo=mi+1;
            }
            Pair p=ps[lo];
            return compareKey(K,p.key)==0?p.val:null;
        }
        public int[] get(long[] K) {
            if (!prepared) throw new RuntimeException();
            searches++;
            if (filters!=null) {
                for (int f=0; f<filters.length; f++) {
                    filterWork[f]++;
                    int v=(int)((K[f/2]>>(filterPow*(f%2)))&filterMask);
                    if (((filters[f][(int)(v>>>6)]>>(v&63))&1)==0) return null;
                }
            }
            return binsearch(K,pairs);
        }
        public long[][] keys() {
            if (!prepared) throw new RuntimeException();
            long[][] out=new long[pairs.length][];
            for (int i = 0; i< pairs.length; i++) out[i]=pairs[i].key;
            return out;
        }
        public int size() {
            if (!prepared) throw new RuntimeException();
            return sz;
        }
    }

    public static void main(String[] args) {
        System.out.println("max heap size="+Runtime.getRuntime().maxMemory());
        System.out.println("m="+memStats());
        /*long stmem=usedMem();
        SplittableRandom rnd=new SplittableRandom(1); {
            List<ArrMap.Pair> l=new ArrayList<>();
            for (int i=0; i<40_000_000; i++) l.add(new ArrMap.Pair(
                    new long[] {rnd.nextLong(),rnd.nextLong(),},
                    new int[] {rnd.nextInt(),rnd.nextInt(),rnd.nextInt(),rnd.nextInt(),}
            ));
            System.out.println("m="+memStats());
            long amt=usedMem()-stmem;
            System.out.println(amt+"; ~"+amt/(double)l.size()+" bytes per Pair");
            ArrMap.Pair[] a=l.toArray(new ArrMap.Pair[0]);
            System.out.println("m="+memStats());
            l.clear();
            System.out.println("m="+memStats());
        }
        System.out.println("m="+memStats());*/

        N=3;
        N2=N*N; N4=N2*N2; N6=N4*N2;

        int MAXMINORRANK=5, MAXNMAJOR=3, MAXMINORNZ=729, MAXMAJORNZ=3;
        String MODE="FLIP";
        System.out.printf("N=%d MAXMINORRANK=%d MAXNMAJOR=%d MAXMINORNZ=%d MAXMAJORNZ=%d MODE=%s%n",N,MAXMINORRANK,MAXNMAJOR,MAXMINORNZ,MAXMAJORNZ,MODE);

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
        int MAXRANK=MAXMINORRANK+MAJOR_GROUP_SIZE*MAXNMAJOR;
        System.out.println("MAJOR_GROUP_SIZE="+MAJOR_GROUP_SIZE+" MAXRANK="+MAXRANK);

        //create the index groups used for tensor compression
        int[] compressionClassNum=new int[N6]; Arrays.fill(compressionClassNum,-1); G=0; {
            int[] log2=new int[1<<N2]; for (int i=0; i<N2; i++) log2[1<<i]=i;
            for (int i=0; i<N2; i++) for (int j=0; j<N2; j++) for (int k=0; k<N2; k++) if (compressionClassNum[i*N4+j*N2+k]==-1) {
                for (int tric:transformedTris(1<<i,1<<j,1<<k))
                    compressionClassNum[log2[tric&MASK]*N4+log2[(tric>>N2)&MASK]*N2+log2[(tric>>(2*N2))&MASK]]=G;
                G++;
            }
        }
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

        //enumerate the resulting tensor of all sparse groups generated from a single matrix triplet
        long[][] groupTensor=new long[1<<(3*N2)][];
        int[] groupSize=new int[1<<(3*N2)];
        int[] majors, minors; {
            System.out.println("generating groups");
            int[] bitcnt=new int[1<<N2];
            bitcnt[0]=0;
            for (int i=1; i<(1<<N2); i++) bitcnt[i]=bitcnt[i/2]+i%2;
            long st=System.currentTimeMillis(), mark=0;
            long work=0;
            int[] groupSzHist=new int[MAJOR_GROUP_SIZE+1];
            boolean[] taken=new boolean[1<<(3*N2)];
            ArrMap majorMap=new ArrMap(), minorMap=new ArrMap();
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
                    if (bitcnt[a]*bitcnt[b]*bitcnt[c]<=(major?MAXMAJORNZ:MAXMINORNZ)) {
                        groupSzHist[S]++;
                        groupSize[triplet]=S;
                        long[] eval=symmCompress(xortensor(triGroup));
                        groupTensor[triplet]=eval;
                        (major?majorMap:minorMap).put(eval,new int[] {triplet});
                    }
                    work++;
                }
            }
            System.out.printf("work=%d t=%d m=%s histogram of sizes=%s end%n",
                    work,System.currentTimeMillis()-st,memStats(),Arrays.toString(groupSzHist));
            majorMap.prepare(false); minorMap.prepare(false);
            class $ {
                public static int[] vals(ArrMap M) {
                    int[] out=new int[M.pairs.length];
                    for (int i=0; i<M.pairs.length; i++) out[i]=M.pairs[i].val[0];
                    return out;
                }
            }
            majors=$.vals(majorMap); minors=$.vals(minorMap);
            System.out.printf("after filtering: majors=%d,minors=%d%n",majors.length,minors.length);
        }
        System.out.println("m="+memStats());

        class TOTRANK {
            private int totrank(int[] tris) {
                int out=0;
                for (int tri:tris) out+=groupSize[tri];
                return out;
            }
        } TOTRANK $=new TOTRANK();
        interface DFSDoer {
            void process(long[] K, int[] tris, int rank);
        }
        class ForEachTripletCombo {
            int[] tripletList;
            int maxRank;
            List<Integer> dfs_tris;
            void dfs(long[] K, int i, int rank, DFSDoer doer) {
                {
                    int[] A=new int[dfs_tris.size()];
                    for (int k=0; k<A.length; k++) A[k]=dfs_tris.get(k);
                    doer.process(K,A,rank);
                }
                if (rank==maxRank || i>=tripletList.length) return;
                for (int j=i; j<tripletList.length; j++) {
                    int tri=tripletList[j];
                    int nrank=rank+groupSize[tri];
                    if (nrank<=maxRank) {
                        dfs_tris.add(tri);
                        dfs(xor(K,groupTensor[tri]),j+1,nrank,doer); //use j+1 b.c. mod 2 means there is no point in having duplicate matrix triplets in decomposition
                        dfs_tris.remove(dfs_tris.size()-1);
                    }
                }
            }
            ForEachTripletCombo(int[] tripletList, int maxRank, DFSDoer doer) {
                this.tripletList=tripletList; this.maxRank=maxRank;
                dfs_tris=new ArrayList<>();
                dfs(symmCompress(new int[N4]),0,0,doer);
            }
        }
        //TODO: IMPLICITLY STORE DFS TREE AS NODE-->PAR ARRAY
        class TripletsComboMap {
            ArrMap map;
            public TripletsComboMap(int[] tris, int maxRank, boolean advanced) {
                System.out.println("max rank="+maxRank);
                long st=System.currentTimeMillis();
                final long[] mark={0}, work={0};
                map=new ArrMap();
                new ForEachTripletCombo(tris,maxRank,new DFSDoer() {
                    public void process(long[] K, int[] tris, int rank) {
                        long time=System.currentTimeMillis()-st;
                        if (time>=mark[0]) {
                            mark[0]+=5000;
                            System.out.printf("work=%d m=%s t=%d%n",work[0],memStats(),time);
                        }
                        work[0]++;
                        map.put(K,tris);
                    }
                });
                System.out.printf("work=%d m=%s t=%d%n",work[0],memStats(),System.currentTimeMillis()-st);
                map.prepare(new Comparator<int[]>() {
                    public int compare(int[] a1, int[] a2) {
                        return $.totrank(a1)-$.totrank(a2);
                    }
                },advanced);
                System.out.println("# tensors after filtering="+map.size());
            }
            int[] comboInfo(int pairIdx) {
                return map.pairs[pairIdx].val;
            }
            int[] comboInfo(long[] K) {
                return map.get(K);
            }
        }

        int MIN0, MAJ0; { //decide how to split the search space to minimize running time (with memory constraints taken into account)
            long[] minDFSamts=new long[MAXMINORRANK+1];
            for (int minr=0; minr<=MAXMINORRANK; minr++) {
                int r=minr;
                new ForEachTripletCombo(minors, minr, new DFSDoer() {
                    public void process(long[] K, int[] tris, int rank) {
                        minDFSamts[r]++;
                    }
                });
            }
            class NcR {
                public static double val(int n, int k) { //return ln( nCr(n,k) )=ln( n!/((n-k)!k!) )
                    double out=0;
                    for (int i=n; i>n-k; i--) out+=Math.log(i);
                    for (int i=1; i<=k; i++) out-=Math.log(i);
                    return out;
                }
            }
            double bscr=Double.POSITIVE_INFINITY;
            double bh0=Double.POSITIVE_INFINITY, bh1=Double.POSITIVE_INFINITY;
            int bmin0=-1, bmaj0=-1;
            for (int min0=0; min0<=MAXMINORRANK; min0++)
                for (int maj0=0; maj0<=MAXNMAJOR; maj0++) {
                    double h0=Math.log(minDFSamts[min0])+NcR.val(majors.length,maj0),
                            h1=Math.log(minDFSamts[MAXMINORRANK-min0])+NcR.val(majors.length,MAXNMAJOR-maj0);
                    if (h0>=h1) {
                        System.out.println(min0+" "+maj0+" "+h0+" "+h1);
                        double scr=Math.max(h0,h1);
                        if (scr<bscr && Math.min(h0,h1)<=Math.log(200_000_000) && Math.log(minDFSamts[min0])<=Math.log(200_000_000)) {
                            bscr=scr;
                            bh0=h0; bh1=h1;
                            bmin0=min0;
                            bmaj0=maj0;
                        }
                    }
                }
            if (bmin0==-1) throw new RuntimeException();
            MIN0=bmin0; MAJ0=bmaj0;
            System.out.printf("search scheme: iterate %d minor + %d major (cost ~e^%.5f), map %d minor %d major (cost ~e^%.5f)%n",
                    MIN0,MAJ0,bh0, MAXMINORRANK-MIN0,MAXNMAJOR-MAJ0,bh1);
        }
        System.out.println("generating min1");
        TripletsComboMap min1DFS=new TripletsComboMap(minors,MAXMINORRANK-MIN0,false);
        System.out.println("generating maj1");
        TripletsComboMap maj1DFS=new TripletsComboMap(majors,MAJOR_GROUP_SIZE*(MAXNMAJOR-MAJ0),false);
        System.out.println("generating h1: m="+memStats());
        ArrMap h1Map=new ArrMap(); {
            long st=System.currentTimeMillis(), mark=0, work=0;
            for (ArrMap.Pair pmin1:min1DFS.map.pairs) for (ArrMap.Pair pmaj1:maj1DFS.map.pairs) {
                long time=System.currentTimeMillis()-st;
                if (time>=mark) {
                    mark+=5000;
                    System.out.printf("work=%d m=%s t=%d%n",work,memStats(),time);
                }
                work++;
                int[] tris=new int[pmin1.val.length+pmaj1.val.length];
                System.arraycopy(pmin1.val,0,tris,0,pmin1.val.length);
                System.arraycopy(pmaj1.val,0,tris,pmin1.val.length,pmaj1.val.length);
                h1Map.put(xor(pmin1.key,pmaj1.key),tris);
            }
            System.out.printf("work=%d m=%s t=%d%n",work,memStats(),System.currentTimeMillis()-st);
            h1Map.prepare(new Comparator<int[]>() {
                public int compare(int[] a1, int[] a2) {
                    return $.totrank(a1)-$.totrank(a2);
                }
            },true);
            System.out.println("# tensors in h1 after filtering="+h1Map.size());
        }

        long[] KTARGET=symmCompress(TARGET);
        final int[] brank={Integer.MAX_VALUE};
        long[] rankHist=new long[MAXRANK+1];
        System.out.println("searching: m="+memStats());
        long st=System.currentTimeMillis();
        final long[] mark={0};
        TripletsComboMap min0=new TripletsComboMap(minors,MIN0,false);
        long[][] Km0s=min0.map.keys();
        String statsString="searches=%d filterWork=%s binSearches=%d binWork=%d m=%s t=%d%n";
        new ForEachTripletCombo(majors, MAJOR_GROUP_SIZE*MAJ0, new DFSDoer() {
            public void process(long[] KM0, int[] trisM0, int rankM0) {
                long time=System.currentTimeMillis()-st;
                if (time>=mark[0]) {
                    mark[0]+=(mark[0]<100_000?10_000:100_000);
                    System.out.printf(statsString,h1Map.searches,Arrays.toString(h1Map.filterWork),h1Map.binSearches,h1Map.binWork,memStats(),time);
                }
                long[] tmp=xor(KTARGET,KM0);
                for (long[] Km0:Km0s) {
                    int[] h1Tris=h1Map.get(xor(tmp,Km0));
                    if (h1Tris!=null) {
                        int[] min0Tris=min0.comboInfo(Km0);
                        int rank=rankM0+$.totrank(min0Tris)+$.totrank(h1Tris);
                        rankHist[rank]++;
                        if (rank<brank[0]) {
                            brank[0]=rank;
                            System.out.println("rank="+rank+" generated from");
                            for (int[] combo:new int[][] {trisM0,min0Tris,h1Tris})
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
        });
        System.out.printf(statsString,h1Map.searches,Arrays.toString(h1Map.filterWork),h1Map.binSearches,h1Map.binWork,memStats(),System.currentTimeMillis()-st);
        System.out.println("rank histogram="+Arrays.toString(rankHist));
    }
}
