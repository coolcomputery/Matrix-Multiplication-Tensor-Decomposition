import java.util.*;
public class SymmetricBruteForce {
    private static int N, N2, N4, N6;
    private static int[] TARGET;
    private static int G;
    private static int[][] groups;
    private static int[] groupNum, groupSzs;
    private static int[][] bounds;
    private static int[] t1nsorCubed(int[] X) {
        return t1nsor(X,X,X);
    }
    private static int[] t1nsor(int[] X, int[] Y, int[] Z) {
        //TODO: IMPROVE CASHE MISSES
        int[] T=new int[N6];
        for (int ab=0; ab<N2; ab++)
            for (int cd=0; cd<N2; cd++)
                for (int ef=0; ef<N2; ef++)
                    T[ab*N4+cd*N2+ef]=X[ab]*Y[cd]*Z[ef];
        return T;
    }
    private static int[] B(int[] M) {
        int[] out=new int[N2];
        for (int i=0; i<N; i++) for (int j=0; j<N; j++)
            out[i*N+j]=M[((i+1)%N)*N+((j+1)%N)];
        return out;
    }
    private static int nnonzero(int[] A) {
        int out=0;
        for (int v:A) if (v!=0) out++;
        return out;
    }
    private static List<int[]> mats(int z) {
        List<int[]> out=new ArrayList<>();
        int[] M=new int[N2]; Arrays.fill(M,-1);
        while (M[N2-1]<2) {
            int n=nnonzero(M); if (n>0&&n<=z) out.add(Arrays.copyOf(M,N2));
            M[0]++;
            for (int i=0; i<N2-1&&M[i]>=2; i++) {
                M[i]=-1;
                M[i+1]++;
            }
        }
        return out;
    }
    private static int[] sum(int[] A, int[] B) {
        if (A.length!=B.length) throw new RuntimeException();
        int[] C=new int[A.length];
        for (int i=0; i<A.length; i++) C[i]=A[i]+B[i];
        return C;
    }
    private static int[] diff(int[] A, int[] B) {
        if (A.length!=B.length) throw new RuntimeException();
        int[] C=new int[A.length];
        for (int i=0; i<A.length; i++) C[i]=A[i]-B[i];
        return C;
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
    private interface ArrMap {
        //efficient map int[] --> smth
        void put(int[] A, int[][] v);
        int[][] get(int[] A);
        List<int[]> keys();
        int size();
    }
    private static class TensorMatricesPair {
        int[] tensor;
        int[][] matrices;
        public TensorMatricesPair(int[] t, int[][] ms) {
            tensor=t; matrices=ms;
        }
    }
    private static List<TensorMatricesPair> pairs(ArrMap map) {
        List<TensorMatricesPair> out=new ArrayList<>();
        for (int[] T:map.keys()) out.add(new TensorMatricesPair(T,map.get(T)));
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
    private static int[] t1nsorRot(int[] A, int[] B, int[] C) {
        return sum(sum(t1nsor(A,B,C),t1nsor(B,C,A)),t1nsor(C,A,B));
    }
    private static int[] t1nsorRotB(int[] M0, int[] M1, int[] M2) {
        int[] B0=B(M0), B1=B(M1), B2=B(M2),
                P0=B(B0), P1=B(B1), P2=B(B2);
        return sum(sum(t1nsorRot(M0,M1,M2),t1nsorRot(B0,B1,B2)),t1nsorRot(P0,P1,P2));
    }
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
    private static String arr2_str(int[][] A) {
        StringBuilder s=new StringBuilder("[");
        for (int[] a:A) s.append(Arrays.toString(a)+" ");
        s.append("]");
        return s.toString();
    }
    private static class TrieArrMap implements ArrMap {
        //TODO: RADIX TREE TO REDUCE MEMORY??????????????
        //          (what about searching for all arr.s within kixed dist. of specific arr.?????
        int[][][] val;
        int[] depth;
        int[][] cidxs;
        int treesz, size;
        public TrieArrMap() {
            treesz=1;
            size=0;
            val=new int[][][] {null};
            depth=new int[] {-1};
            cidxs=new int[][] {null};
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
            treesz++;
        }
        private void createChildOf(int i, int b) {
            //create a child of node i, where the branch to this child is associated with the number b
            if (childOf(i,b)>=0) throw new RuntimeException("node "+i+" already has child on branch of value "+b);
            int d=depth[i];
            if (d==G-1) throw new RuntimeException("node is designated leaf");
            int l=bounds[d+1][0], r=bounds[d+1][1];
            if (b<l||b>r) throw new RuntimeException("child branch value "+b+" not in range ["+l+","+r+"]");
            if (cidxs[i]==null) {
                cidxs[i]=new int[r-l+1];
                Arrays.fill(cidxs[i],-1);
            }
            addNode(d+1);
            cidxs[i][b-l]=treesz-1;
        }
        private int childOf(int i, int b) {
            if (i<0||i>=treesz) throw new RuntimeException();
            return cidxs[i]==null||b<bounds[depth[i]+1][0]||b>bounds[depth[i]+1][1]?-1:
                    cidxs[i][b-bounds[depth[i]+1][0]];
        }
        public void put(int[] A, int[][] v) {
            if (A.length!=G) throw new RuntimeException();
            int i=0;
            boolean added=false;
            for (int b:A) {
                if (childOf(i,b)<0) {
                    createChildOf(i,b);
                    added=true;
                }
                i=childOf(i,b);
            }
            val[i]=v;
            if (added) size++;
        }
        public int[][] get(int[] A) {
            int i=0;
            for (int b:A) {
                i=childOf(i,b);
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
            if (d<bounds.length-1)
            for (int b=bounds[d+1][0]; b<=bounds[d+1][1]; b++) if (childOf(i,b)<0) {
                stack.add(b);
                dfs(childOf(i,b));
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
    private static class Searcher {
        //search through all of map's keys that are of distance <=D from CT
        //  and return the key of closest distance to CT
        static TrieArrMap map;
        static int[] CT, stack, ret;
        static int D, bestDist;
        private static void search_help(int i, int d, int dist) {
            if (i<0) return;
            if (d==G) {
                if (dist<bestDist) {
                    bestDist=dist;
                    ret=Arrays.copyOf(stack,G);
                }
                return;
            }
            int match_b=CT[d];
            stack[d]=match_b;
            search_help(map.childOf(i,match_b),d+1,dist);
            int ndist=dist+groupSzs[d];
            if (ndist<=D)
            for (int b=bounds[d][0]; b<=bounds[d][1]; b++) if (b!=match_b) {
                stack[d]=b;
                search_help(map.childOf(i,b),d+1,ndist);
            }
        }
        public static int[][] closestWithin(TrieArrMap map, int[] CT, int D) {
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
    private static int[] neg(int[] M) {
        int[] out=new int[M.length];
        for (int i=0; i<M.length; i++) out[i]=-M[i];
        return out;
    }
    public static void main(String[] args) {
        System.out.println("max heap size="+Runtime.getRuntime().maxMemory());
        System.out.println("current heap usage="+Runtime.getRuntime().totalMemory());
        N=3;
        N2=N*N; N4=N2*N2; N6=N4*N2;
        int R=2, Z=4, D=6;
        System.out.printf("R=%d,Z=%d,D=%d%n",R,Z,D);

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
        /*for (int[] group:groups) {
            for (int i:group) {
                int[] coords=new int[6];
                for (int h=i, a=0; a<6; a++, h/=N) coords[5-a]=h%N;
                System.out.print(Arrays.toString(coords)+" ");
            }
            System.out.println();
        }*/

        TARGET=new int[N6];
        for (int i=0; i<N; i++) for (int j=0; j<N; j++) for (int k=0; k<N; k++)
            TARGET[(i*N+j)*N4+(j*N+k)*N2+(k*N+i)]=1;
        int[] CTARGET=compress(TARGET);
        //cyc3 + cycperm symmetries
        //A: turns XxYxZ tensor into YxZxX
        //B: turns XxYxZ into P(X)xP(Y)xP(Z),
        long st=System.currentTimeMillis();
        List<int[]> MATS=mats(N*N), BATS=new ArrayList<>(); {
            for (int[] M:mats(N*N)) if (Arrays.equals(M,B(M))) BATS.add(M);
        }
        System.out.println(MATS.size()+" MATS, "+BATS.size()+" BATS");

        List<TensorMatricesPair> Gab, Ga, Gb; {
            ArrMap m=new MapArrMap();
            for (int[] BM:BATS) m.put(compress(t1nsorCubed(BM)),new int[][] {BM});
            Gab=pairs(m);
        } {
            ArrMap m=new MapArrMap();
            for (int[] M:MATS) {
                int[] B=B(M), B2=B(B);
                m.put(compress(sum(sum(t1nsorCubed(M),t1nsorCubed(B)),t1nsorCubed(B2))),new int[][] {M});
            }
            Ga=pairs(m);
        } {
            ArrMap m=new MapArrMap();
            for (int[] B0:BATS) for (int[] B1:BATS) for (int[] B2:BATS)
                m.put(compress(sum(sum(t1nsor(B0,B1,B2),t1nsor(B1,B2,B0)),t1nsor(B2,B0,B1))),new int[][] {B0,B1,B2});
            Gb=pairs(m);
        }
        System.out.println(Gab.size()+" Gab, "+Ga.size()+" Ga, "+Gb.size()+" Gb");
        System.out.println("init time="+(System.currentTimeMillis()-st));
        System.out.println("current heap usage="+Runtime.getRuntime().totalMemory());

        int Rminor=23-9*R;
        bounds=new int[G][2];
        for (int g=0; g<G; g++) {
            bounds[g][1]=CTARGET[g]+Rminor;
            bounds[g][0]=CTARGET[g]-Rminor;
        }

        st=System.currentTimeMillis();
        TrieArrMap minorMap=new TrieArrMap(); {
            long mark=0;
            long work=0;
            System.out.println("minor part has rank<="+Rminor);
            System.out.println("Rab,Ra,Rb");
            for (int Rab=0; Rab<Gab.size() && Rab<=Rminor; Rab++)
            for (int Ra=0; Ra<Ga.size() && Rab+3*Ra<=Rminor; Ra++)
            for (int Rb=0; Rb<Gb.size() && Rab+3*Ra+3*Rb<=Rminor; Rb++) {
                List<int[]> Cabs=combos_with_replacement(Gab.size(),Rab),
                        Cas=combos_with_replacement(Ga.size(),Ra),
                        Cbs=combos_with_replacement(Gb.size(),Rb);
                System.out.printf("%d,%d,%d (cnt=%d)%n",Rab,Ra,Rb,(long)Cabs.size()*Cas.size()*Cbs.size());
                for (int[] Cab:Cabs) for (int[] Ca:Cas) for (int[] Cb:Cbs) {
                    work++;
                    int[] T=new int[G];
                    for (int iab:Cab) T=sum(T,Gab.get(iab).tensor);
                    for (int ia:Ca) T=sum(T,Ga.get(ia).tensor);
                    for (int ib:Cb) T=sum(T,Gb.get(ib).tensor);
                    T=diff(CTARGET,T);
                    int[][] info=minorMap.get(T);
                    int pscr=info==null?Integer.MAX_VALUE:info[0].length+3*info[1].length+3*info[2].length;
                    if (Cab.length+3*Ca.length+3*Cb.length<pscr)
                        minorMap.put(T,new int[][] {Cab,Ca,Cb});
                    long time=System.currentTimeMillis()-st;
                    if (time>=mark) {
                        System.out.println(time+" "+work+" "+minorMap.size()+" "+minorMap.nodeCnt()+" "+Runtime.getRuntime().totalMemory());
                        mark+=10_000;
                    }
                }
                long time=System.currentTimeMillis()-st;
                System.out.println(time+" "+work+" "+minorMap.size()+" "+minorMap.nodeCnt()+" "+Runtime.getRuntime().totalMemory());
            }
            long time=System.currentTimeMillis()-st;
            System.out.println(time+" "+work+" "+minorMap.size()+" "+minorMap.nodeCnt()+" "+Runtime.getRuntime().totalMemory());
        }
        System.out.println("minorMap creation time="+(System.currentTimeMillis()-st));

        System.out.println("starting search");
        Map<String,String> canonicalForm=new HashMap<>();
        List<int[]> canonicalMATS=new ArrayList<>();
        for (int[] M:MATS) {
            String code=Arrays.toString(M);
            String cancode=code;
            for (int[] M1:new int[][] {M,B(M),B(B(M))})
                for (int[] nM:new int[][] {M1,neg(M1)}) {
                    String ncode=Arrays.toString(nM);
                    if (ncode.compareTo(cancode)<0) cancode=ncode;
                }
            canonicalForm.put(code,cancode);
            if (code.equals(cancode))
                canonicalMATS.add(M);
        }

        st=System.currentTimeMillis();
        List<int[][]> canonicalTriplets=new ArrayList<>();
        for (int[] M0:canonicalMATS) {
            int z0=nnonzero(M0);
            if (z0<=Z) {
                String cancode0=canonicalForm.get(Arrays.toString(M0));
                List<int[]> rems=new ArrayList<>();
                for (int[] M:MATS)
                    if (cancode0.compareTo(canonicalForm.get(Arrays.toString(M)))<=0)
                        rems.add(M);
                for (int[] M1:rems) {
                    int z1=nnonzero(M1);
                    if (z0*z1<=Z && Arrays.toString(M1).compareTo(Arrays.toString(neg(M1)))<=0)
                        for (int[] M2:rems)
                            if (z0*z1*nnonzero(M2)<=Z)
                                canonicalTriplets.add(new int[][] {M0,M1,M2,compress(t1nsorRotB(M0,M1,M2))});
                }
            }
        }
        System.out.println("# triplets="+canonicalTriplets.size());
        System.out.println("triplets creation time="+(System.currentTimeMillis()-st));
        canonicalTriplets.add(null);

        st=System.currentTimeMillis(); long mark=0;
        int bscr=Integer.MAX_VALUE;
        long work=0;
        for (int triAi=0; triAi<canonicalTriplets.size()-1; triAi++)
            for (int triBi=triAi; triBi<canonicalTriplets.size(); triBi++) {
                int[][] triA=canonicalTriplets.get(triAi), triB=canonicalTriplets.get(triBi);
                long time=System.currentTimeMillis()-st;
                if (time>mark) {
                    mark+=100_000;
                    System.out.println(time+" "+work);
                }
                work++;
                int[] CT=triB==null?triA[3]:sum(triA[3],triB[3]);
                int[][] aCT=Searcher.closestWithin(minorMap,CT,D);
                if (aCT[0]!=null) {
                    int scr=aCT[1][0];
                    if (scr<bscr) {
                        int[][] info=minorMap.get(aCT[0]);
                        bscr=scr;
                        System.out.println("scr="+scr);
                        System.out.println("Gab"); for (int iab:info[0]) System.out.println(arr2_str(Gab.get(iab).matrices));
                        System.out.println("Ga"); for (int ia:info[1]) System.out.println(arr2_str(Ga.get(ia).matrices));
                        System.out.println("Gb"); for (int ib:info[2]) System.out.println(arr2_str(Gb.get(ib).matrices));
                        System.out.println("G"); for (int[][] tri:new int[][][] {triA,triB}) if (tri!=null) System.out.println(arr2_str(Arrays.copyOf(tri,3)));
                    }
                }
            }
        System.out.println("work="+work);
        System.out.println("search time="+(System.currentTimeMillis()-st));
    }
}