import java.util.*;
//same as SymmetricBruteForce.java, but everything is mod 2
public class SymmetricMod2 {
    //TODO: BIT TWIDDLING TRICKS
    private static int mod2(int n) {
        return (n%2+2)%2;
    }
    private static int N, N2, N4, N6;
    private static int[] TARGET;
    private static int[] t1nsor(int[] X, int[] Y, int[] Z) {
        //TODO: IMPROVE CACHE MISSES
        int[] T=new int[N6];
        for (int ab=0; ab<N2; ab++)
            for (int cd=0; cd<N2; cd++)
                for (int ef=0; ef<N2; ef++)
                    T[ab*N4+cd*N2+ef]=X[ab]*Y[cd]*Z[ef];
        return T;
    }
    private static int[] t1nsor(int[][] tri) {
        return t1nsor(tri[0],tri[1],tri[2]);
    }
    private static int[] sum(int[] A, int[] B) {
        if (A.length!=B.length) throw new RuntimeException();
        int[] C=new int[A.length];
        for (int i=0; i<A.length; i++) C[i]=mod2(A[i]+B[i]);
        return C;
    }
    private static int[] sumdecomp(List<int[][]> tris) {
        int[] out=new int[N6];
        for (int[][] tri:tris) out=sum(out,t1nsor(tri));
        return out;
    }
    private static int[] diff(int[] A, int[] B) {
        if (A.length!=B.length) throw new RuntimeException();
        int[] C=new int[A.length];
        for (int i=0; i<A.length; i++) C[i]=mod2(A[i]-B[i]);
        return C;
    }

    private static int G;
    private static int[][] groups;
    private static int[] groupNum, groupSzs;
    private static int[] compress(int[] T) {
        int[] out=new int[G];
        for (int g=0; g<G; g++) {
            int[] group=groups[g];
            int v=T[group[0]];
            for (int i:group) if (v!=T[i]) throw new RuntimeException("Tensor not symmetric enough for compression.");
            out[g]=v;
        }
        return out;
    }

    private static int nnonzero(int[] A) {
        int out=0;
        for (int v:A) if (v!=0) out++;
        return out;
    }
    private static List<int[]> mats(int z) {
        List<int[]> out=new ArrayList<>();
        int[] M=new int[N2];
        while (M[N2-1]<2) {
            int n=nnonzero(M); if (n>0&&n<=z) out.add(Arrays.copyOf(M,N2));
            M[0]++;
            for (int i=0; i<N2-1&&M[i]>=2; i++) {
                M[i]=0;
                M[i+1]++;
            }
        }
        return out;
    }
    private static int[] $(int[] M, int s) {
        int[] out=new int[N2];
        for (int i=0; i<N; i++) for (int j=0; j<N; j++)
            out[((i+s)%N)*N+((j+s)%N)]=M[i*N+j];
        return out;
    }
    private static List<int[][]> expandC(List<int[][]> triplets) {
        List<int[][]> out=new ArrayList<>();
        for (int[][] tri:triplets) {
            int[] A=tri[0], B=tri[1], C=tri[2];
            out.addAll(Arrays.asList(new int[][] {A,B,C},new int[][] {B,C,A},new int[][] {C,A,B}));
        }
        return out;
    }
    private static List<int[][]> expand$(List<int[][]> triplets) {
        List<int[][]> out=new ArrayList<>();
        for (int[][] tri:triplets)
            for (int s=0; s<N; s++)
                out.add(new int[][] {$(tri[0],s),$(tri[1],s),$(tri[2],s)});
        return out;
    }

    private static List<int[]> combos_with_replacement(int N, int K) {
        //output a list of all sorted K-length combinations of numbers 0...N-1,
        //  where duplicates are allowed
        List<List<List<int[]>>> ls=new ArrayList<>();
        for (int n=0; n<=N; n++) {
            ls.add(new ArrayList<>());
            for (int k=0; k<=K; k++) {
                List<int[]> ret;
                if (k==0) ret=new ArrayList<>(Collections.singletonList(new int[0]));
                else if (n<=0) ret=new ArrayList<>();
                else {
                    ret=ls.get(n-1).get(k);
                    for (int[] c:ls.get(n).get(k-1)) {
                        int[] nc=Arrays.copyOf(c,k);
                        nc[k-1]=n-1;
                        ret.add(nc);
                    }
                }
                ls.get(n).add(ret);
            }
        }
        return ls.get(N).get(K);
    }

    private static String arr2_str(int[][] A) {
        StringBuilder s=new StringBuilder("[");
        for (int[] a:A) s.append(Arrays.toString(a)+" ");
        s.append("]");
        return s.toString();
    }

    private static class MapArrMap implements ArrMap {
        Map<String,int[][]> m;
        public MapArrMap() {
            m=new HashMap<>();
        }
        public void put(int[] A, int[][] v) {
            m.put(Arrays.toString(A),v);
        }
        public int[][] get(int[] A) {
            return m.get(Arrays.toString(A));
        }
        public List<int[]> keys() {
            List<int[]> out=new ArrayList<>();
            for (String s:m.keySet()) {
                String[] info=s.substring(1,s.length()-1).split(", ");
                int[] a=new int[info.length];
                for (int i=0; i<a.length; i++) a[i]=Integer.parseInt(info[i]);
                out.add(a);
            }
            return out;
        }
        public int size() {
            return m.size();
        }
    }
    private static class BinaryTrieArrMap implements ArrMap {
        //TODO: RADIX TREE TO REDUCE MEMORY?
        //          (what about searching for all arr.s within kixed dist. of specific arr.?????
        int[][][] val;
        int[] depth;
        int[][] cidxs;
        int treesz, size;
        public BinaryTrieArrMap() {
            treesz=1;
            size=0;
            val=new int[][][] {null};
            depth=new int[] {-1};
            cidxs=new int[][] {{-1,-1}};
        }
        private void addNode(int d) {
            if (treesz==val.length) {
                int len=val.length;
                len=Math.max(len+1,2*len);
                val=Arrays.copyOf(val,len);
                depth=Arrays.copyOf(depth,len);
                cidxs=Arrays.copyOf(cidxs,len);
            }
            depth[treesz]=d;
            cidxs[treesz]=new int[] {-1,-1};
            treesz++;
        }
        private void createChildOf(int i, int b) {
            //create a child of node i, where the branch to this child is associated with the number b
            int d=depth[i];
            if (d==G-1) throw new RuntimeException("node is designated leaf");
            if (cidxs[i][b]>=0) throw new RuntimeException("node "+i+" already has child on branch of value "+b);
            addNode(d+1);
            cidxs[i][b]=treesz-1;
        }
        public void put(int[] A, int[][] v) {
            if (A.length!=G) throw new RuntimeException();
            int i=0;
            boolean added=false;
            for (int b:A) {
                if (cidxs[i][b]<0) {
                    createChildOf(i,b);
                    added=true;
                }
                i=cidxs[i][b];
            }
            val[i]=v;
            if (added) size++;
        }
        public int[][] get(int[] A) {
            int i=0;
            for (int b:A) {
                i=cidxs[i][b];
                if (i<0) return null;
            }
            return val[i];
        }
        List<int[]> keys;
        List<Integer> stack;
        private void dfs(int i) {
            if (val[i]!=null) {
                int[] A=new int[stack.size()];
                for (int b=0; b<A.length; b++) A[b]=stack.get(b);
                keys.add(A);
            }
            int d=depth[i];
            if (d<G-1)
                for (int b=0; b<2; b++) if (cidxs[i][b]<0) {
                    stack.add(b);
                    dfs(cidxs[i][b]);
                    stack.remove(stack.size()-1);
                }
        }
        public List<int[]> keys() {
            stack=new ArrayList<>();
            keys=new ArrayList<>();
            dfs(0);
            return keys;
        }
        public int size() {
            return size;
        }
        public int nodeCnt() {
            return treesz;
        }
    }
    private interface ArrMap {
        //efficient map int[] --> smth
        void put(int[] A, int[][] v);
        int[][] get(int[] A);
        List<int[]> keys();
        int size();
    }
    private static long search_work;
    private static class Searcher {
        //search through all of map's keys that are of distance <=D from CT
        //  and return the key of closest distance to CT
        static BinaryTrieArrMap map;
        static int[] CT, stack, ret;
        static int D, bestDist;
        private static void search_help(int i, int d, int dist) {
            search_work++;
            if (i<0) return;
            if (d==G) {
                if (dist<bestDist) {
                    bestDist=dist;
                    ret=Arrays.copyOf(stack,G);
                }
                return;
            }
            int match_b=CT[d];
            int mc=map.cidxs[i][match_b];
            if (mc>-1) {
                stack[d]=match_b;
                search_help(mc,d+1,dist);
            }
            int ndist=dist+groupSzs[d];
            if (ndist<=D) {
                int b=1-match_b;
                int oc=map.cidxs[i][b];
                if (oc>-1) {
                    stack[d]=b;
                    search_help(oc,d+1,ndist);
                }
            }
        }
        public static int[][] closestWithin(BinaryTrieArrMap map, int[] CT, int D) {
            Searcher.map=map;
            Searcher.CT=CT;
            Searcher.D=D;
            ret=null;
            bestDist=D+1;
            stack=new int[G];
            search_help(0,0,0);
            return new int[][] {ret,{bestDist}};
        }
    }

    public static void main(String[] args) {
        System.out.println("max heap size="+Runtime.getRuntime().maxMemory());
        System.out.println("current heap usage="+Runtime.getRuntime().totalMemory());
        N=3;
        N2=N*N; N4=N2*N2; N6=N4*N2;
        TARGET=new int[N6];
        for (int i=0; i<N; i++) for (int j=0; j<N; j++) for (int k=0; k<N; k++)
            TARGET[(i*N+j)*N4+(j*N+k)*N2+(k*N+i)]=1;
        int R=2, Z=16, D=6;
        System.out.printf("N=%d,R=%d,Z=%d,D=%d%n",N,R,Z,D);

        groupNum=new int[N6]; Arrays.fill(groupNum,-1);
        G=0;
        for (int i=0; i<N2; i++) for (int j=0; j<N2; j++) for (int k=0; k<N2; k++) if (groupNum[i*N4+j*N2+k]==-1) {
            for (int rot=0; rot<3; rot++) {
                int[] coords=rot==0?new int[] {i,j,k}:rot==1?new int[] {j,k,i}:new int[] {k,i,j};
                for (int shift=0; shift<N; shift++) {
                    int[] scoords=new int[3];
                    for (int a=0; a<3; a++) scoords[a]=((coords[a]/N+shift)%N)*N+(coords[a]%N+shift)%N;
                    groupNum[scoords[0]*N4+scoords[1]*N2+scoords[2]]=G;
                }
            }
            G++;
        }
        groupSzs=new int[G];
        for (int i=0; i<N6; i++) groupSzs[groupNum[i]]++;
        groups=new int[G][]; {
            for (int g=0; g<G; g++) groups[g]=new int[groupSzs[g]];
            int[] tmp=new int[G];
            for (int i=0; i<N6; i++) {
                int g=groupNum[i];
                groups[g][tmp[g]++]=i;
            }
            int tot=0;
            for (int sz:groupSzs) tot+=sz;
            if (tot!=N6) throw new RuntimeException();
        }
        int[] CTARGET=compress(TARGET);

        List<int[]> MATS=mats(N*N), $MATS=new ArrayList<>();
        for (int[] M:mats(N*N)) if (Arrays.equals(M,$(M,1))) $MATS.add(M);
        System.out.println(MATS.size()+" MATS, "+$MATS.size()+" $MATS");

        System.out.println("making partially symmetric tensor groups");
        ArrMap mapAll=new MapArrMap(), mapC=new MapArrMap(), map$=new MapArrMap(), map$C=new MapArrMap(), map$CC=new MapArrMap();
        for (int[] $:$MATS) mapAll.put(compress(sumdecomp(Collections.singletonList(new int[][] {$,$,$}))),new int[][] {$});
        for (int[] M:MATS) mapC.put(compress(sumdecomp(expand$(Collections.singletonList(new int[][] {M,M,M})))),new int[][] {M});
        for (int[] $0:$MATS) for (int[] $1:$MATS) for (int[] $2:$MATS)
            map$.put(compress(sumdecomp(expandC(Collections.singletonList(new int[][] {$0,$1,$2})))),new int[][] {$0,$1,$2});
        for (int[] M:MATS) map$C.put(compress(sumdecomp(expandC(Collections.singletonList(new int[][] {$(M,2),$(M,1),M})))),new int[][] {M});
        for (int[] M:MATS) map$CC.put(compress(sumdecomp(expandC(Collections.singletonList(new int[][] {M,$(M,1),$(M,2)})))),new int[][] {M});
        System.out.printf("%d All, %d C, %d $, %d $C, %d $CC%n",mapAll.size(),mapC.size(),map$.size(),map$C.size(),map$CC.size());

        System.out.println("making mapMinor");
        List<int[]> kAll=mapAll.keys(), kC=mapC.keys(), k$=map$.keys(), k$C=map$C.keys(), k$CC=map$CC.keys();
        int Rminor=23-9*R;
        BinaryTrieArrMap mapMinor=new BinaryTrieArrMap(); {
            long st=System.currentTimeMillis(), mark=0;
            long work=0;
            for (int sAll=0; sAll<=Rminor; sAll++)
                for (int sC=0; 3*sC<=Rminor; sC++)
                    for (int s$=0; 3*s$<=Rminor; s$++)
                        for (int s$C=0; 3*s$C<=Rminor; s$C++)
                            for (int s$CC=0; 3*s$CC<=Rminor; s$CC++) if (sAll+3*(sC+s$+s$C+s$CC)<=Rminor) {
                                System.out.printf("%d %d %d %d %d%n",sAll,sC,s$,s$C,s$CC);
                                List<int[]> lcAll=combos_with_replacement(mapAll.size(),sAll),
                                        lcC=combos_with_replacement(mapC.size(),sC),
                                        lc$=combos_with_replacement(map$.size(),s$),
                                        lc$C=combos_with_replacement(map$C.size(),s$C),
                                        lc$CC=combos_with_replacement(map$CC.size(),s$CC);
                                for (int[] cAll:lcAll) for (int[] cC:lcC) for (int[] c$:lc$) for (int[] c$C:lc$C) for (int[] c$CC:lc$CC) {
                                    work++;
                                    int[] T=new int[G];
                                    for (int i:cAll) T=sum(T,kAll.get(i));
                                    for (int i:cC) T=sum(T,kC.get(i));
                                    for (int i:c$) T=sum(T,k$.get(i));
                                    for (int i:c$C) T=sum(T,k$C.get(i));
                                    for (int i:c$CC) T=sum(T,k$CC.get(i));
                                    T=diff(CTARGET,T);
                                    int[][] info=mapMinor.get(T);
                                    if (info==null || sAll+3*(sC+s$+s$C+s$CC)<info[0].length+3*(info[1].length+info[2].length+info[3].length+info[4].length))
                                        mapMinor.put(T,new int[][] {cAll,cC,c$,c$C,c$CC});
                                    long time=System.currentTimeMillis()-st;
                                    if (time>=mark) {
                                        mark+=5000;
                                        System.out.printf("%d %d %d%n",work,mapMinor.size(),time);
                                    }
                                }
                                //work+=(long)lcAll.size()*lcC.size()*lc$.size()*lc$C.size()*lc$CC.size();
                                System.out.printf("%d %d %d%n",work,mapMinor.size(),System.currentTimeMillis()-st);
                            }
            System.out.printf("%d %d %d%n",work,mapMinor.size(),System.currentTimeMillis()-st);
        }

        System.out.println("making mapMajor");
        ArrMap mapMajor=new MapArrMap(); {
            long st=System.currentTimeMillis(), mark=0;
            long work=0;
            for (int[] A:MATS) {
                int nzA=nnonzero(A);
                if (nzA<=Z)
                    for (int[] B:MATS) {
                        int nzB=nnonzero(B);
                        if (nzA*nzB<=Z)
                            for (int [] C:MATS) if (nzA*nzB*nnonzero(C)<=Z) {
                                mapMajor.put(compress(sumdecomp(expand$(expandC(Collections.singletonList(new int[][] {A,B,C}))))),new int[][] {A,B,C});
                                work++;
                                long time=System.currentTimeMillis()-st;
                                if (time>=mark) {
                                    mark+=5000;
                                    System.out.printf("%d %d %d%n",work,mapMajor.size(),time);
                                }
                            }
                    }
            }
            System.out.printf("%d %d %d%n",work,mapMajor.size(),System.currentTimeMillis()-st);
        }

        System.out.println("searching");
        long st=System.currentTimeMillis(), mark=0;
        int bscr=Integer.MAX_VALUE;
        long work=0;
        search_work=0;
        if (R==2) {
            long[] histogram=new long[D+1];
            List<int[]> kMajor=mapMajor.keys();
            for (int majAi=0; majAi<kMajor.size(); majAi++)
                for (int majBi=majAi; majBi<kMajor.size(); majBi++) {
                    int[] majA=kMajor.get(majAi), majB=kMajor.get(majBi);
                    int[] CT=sum(majA,majB);
                    int[][] aCT=Searcher.closestWithin(mapMinor,CT,D);
                    if (aCT[0]!=null) {
                        int scr=aCT[1][0];
                        histogram[scr]++;
                        if (scr<bscr) {
                            bscr=scr;
                            int[][] info=mapMinor.get(aCT[0]);
                            System.out.println("scr="+scr);
                            System.out.println("All"); for (int i:info[0]) System.out.println(arr2_str(mapAll.get(kAll.get(i))));
                            System.out.println("C"); for (int i:info[1]) System.out.println(arr2_str(mapC.get(kC.get(i))));
                            System.out.println("$"); for (int i:info[2]) System.out.println(arr2_str(map$.get(k$.get(i))));
                            System.out.println("$C"); for (int i:info[3]) System.out.println(arr2_str(map$C.get(k$C.get(i))));
                            System.out.println("$CC"); for (int i:info[4]) System.out.println(arr2_str(map$CC.get(k$CC.get(i))));
                            System.out.println("major"); for (int[] K:new int[][] {majA,majB}) System.out.println(arr2_str(mapMajor.get(K)));
                        }
                    }
                    long time=System.currentTimeMillis()-st;
                    if (time>=mark) {
                        mark+=100_000;
                        System.out.printf("%d %d %d%n",work,search_work,time);
                    }
                    work++;
                }
            System.out.printf("%d %d %d%n",work,search_work,System.currentTimeMillis()-st);
            System.out.println("histogram="+Arrays.toString(histogram));
        }
    }
}
