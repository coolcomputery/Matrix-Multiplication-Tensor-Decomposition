import java.util.*;
//same as SymmetricBruteForce.java, but everything is mod 2
public class SymmetricMod2 {
    private static String trimat2str(int[][] A) {
        StringBuilder s=new StringBuilder("(");
        for (int[] a:A) s.append(Arrays.toString(a).replace(" ","")+",");
        s.deleteCharAt(s.length()-1);
        s.append("),");
        return s.toString();
    }

    private static int N, N2, N4, N6;
    private static int[] TARGET;
    private static int MASK;
    private static int[] $matcode;
    private static int[] t1nsor(int[] X, int[] Y, int[] Z) {
        //TODO: IMPROVE CACHE MISSES
        int[] T=new int[N6];
        for (int ab=0; ab<N2; ab++) if (X[ab]!=0)
            for (int cd=0; cd<N2; cd++) if (Y[cd]!=0)
                for (int ef=0; ef<N2; ef++) if (Z[ef]!=0)
                    T[ab*N4+cd*N2+ef]=X[ab]*Y[cd]*Z[ef];
        return T;
    }
    private static int[] t1nsor(int[][] tri) {
        return t1nsor(tri[0],tri[1],tri[2]);
    }
    private static int[] sum(int[] A, int[] B) {
        if (A.length!=B.length) throw new RuntimeException();
        int[] C=new int[A.length];
        for (int i=0; i<A.length; i++) C[i]=(A[i]+B[i])%2;
        return C;
    }
    private static int[] sumdecomp(List<int[][]> tris) {
        int[] out=new int[N6];
        for (int[][] tri:tris) out=sum(out,t1nsor(tri));
        return out;
    }

    private static int G;
    private static int[][] groups;
    private static int[] groupNum, groupSzs;
    private static int[] CTARGET;
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

    private static int[] $(int[] M, int s) {
        int[] out=new int[N2];
        for (int i=0; i<N; i++) for (int j=0; j<N; j++)
            out[i*N+j]=M[((i+s)%N)*N+((j+s)%N)];
        return out;
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
    private static int mat2bin(int[] M) {
        int b=0;
        for (int i=0; i<N2; i++) b|=M[i]<<i;
        return b;
    }
    private static int[] bin2mat(int b) {
        int[] M=new int[N2];
        for (int i=0; i<N2; i++) M[i]=(b>>i)&1;
        return M;
    }
    private static int[][] bin2trimat(int c) {
        int xc=c&MASK, yc=(c>>N2)&MASK, zc=(c>>(2*N2))&MASK;
        return new int[][] {bin2mat(xc),bin2mat(yc),bin2mat(zc)};
    }

    private static int[] tri_group_codes(int xcode, int ycode, int zcode) {
        int[] transformed_tri_codes=new int[3*N];
        for (int shift=0, idx=0; shift<N; shift++)
            for (int[] tri0:new int[][] {{xcode,ycode,zcode},{ycode,zcode,xcode},{zcode,xcode,ycode}}) {
                int[] tri=new int[3];
                for (int a=0; a<3; a++) {
                    int code=tri0[a];
                    for (int rep=0; rep<shift; rep++) code=$matcode[code];
                    tri[a]=code;
                }
                transformed_tri_codes[idx++]=tri[0]|(tri[1]<<N2)|(tri[2]<<(2*N2));
            }
        Arrays.sort(transformed_tri_codes);

        int[] out=new int[transformed_tri_codes.length];
        int S=0;
        for (int i=0; i<transformed_tri_codes.length; i++)
            if (i==0 || transformed_tri_codes[i]>transformed_tri_codes[i-1])
                out[S++]=transformed_tri_codes[i];
        return Arrays.copyOf(out,S);
    }
    private static List<int[][]> tricodes2trimats(int[] codes) {
        List<int[][]> out=new ArrayList<>();
        for (int c:codes) out.add(bin2trimat(c));
        return out;
    }

    private static class BinaryTrieArrMap implements ArrMap {
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
            int c0=map.cidxs[i][0], c1=map.cidxs[i][1];
            if (c1>-1) {
                int d1=dist+(CT[d]==1?0:groupSzs[d]);
                if (d1<=D) {
                    stack[d]=1;
                    search_help(c1,d+1,d1);
                }
            }
            if (c0>-1) {
                int d0=dist+(CT[d]==0?0:groupSzs[d]);
                if (d0<=D) {
                    stack[d]=0;
                    search_help(c0,d+1,d0);
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

    private static int MAX_Rminor;
    private static BinaryTrieArrMap minorMap;
    private static int nMinor;
    private static List<int[]> minorGroupTensors;
    private static List<Integer> minorGroupSizes;
    private static List<Integer> dfs_info;
    private static long TIME_ST, TIME_MARK, dfs_work;
    private static void generateMinorMap(int[] CT, int i, int rank) {
        long time=System.currentTimeMillis()-TIME_ST;
        if (time>TIME_MARK) {
            TIME_MARK+=1000;
            System.out.printf("%d %d %d%n",time,dfs_work,minorMap.size());
        }
        dfs_work++;
        if (i>=nMinor) return;
        int nrank=rank+minorGroupSizes.get(i);
        if (nrank<=MAX_Rminor) {
            dfs_info.add(i);
            int[] nCT=sum(CT,minorGroupTensors.get(i));
            int[] K=sum(CTARGET,nCT); //A-B == A+B mod 2
            if (minorMap.get(K)==null || minorMap.get(K)[1][0]>nrank) {
                int[] info_arr=new int[dfs_info.size()];
                for (int j=0; j<info_arr.length; j++) info_arr[j]=dfs_info.get(j);
                minorMap.put(K,new int[][] {info_arr,{nrank}});
            }
            generateMinorMap(nCT,i,nrank);
            dfs_info.remove(dfs_info.size()-1);
        }
        generateMinorMap(CT,i+1,rank);
    }

    public static void main(String[] args) {
        System.out.println("max heap size="+Runtime.getRuntime().maxMemory());
        System.out.println("current heap usage="+Runtime.getRuntime().totalMemory());
        N=3;
        N2=N*N; N4=N2*N2; N6=N4*N2;
        TARGET=new int[N6];
        for (int i=0; i<N; i++) for (int j=0; j<N; j++) for (int k=0; k<N; k++)
            TARGET[(i*N+j)*N4+(j*N+k)*N2+(k*N+i)]=1;
        MASK=(1<<N2)-1;
        $matcode=new int[1<<N2];
        for (int b=1; b<(1<<N2); b++) $matcode[b]=mat2bin($(bin2mat(b),1));

        int R=2, MAXNZ=16, MAXDIST=6;
        System.out.printf("N=%d,R=%d,MAXNZ=%d,MAXDIST=%d%n",N,R,MAXNZ,MAXDIST);

        groupNum=new int[N6]; Arrays.fill(groupNum,-1); G=0; {
            int[] log2=new int[1<<N2]; for (int i=0; i<N2; i++) log2[1<<i]=i;
            for (int i=0; i<N2; i++) for (int j=0; j<N2; j++) for (int k=0; k<N2; k++) if (groupNum[i*N4+j*N2+k]==-1) {
                for (int tric:tri_group_codes(1<<i,1<<j,1<<k))
                    groupNum[log2[tric&MASK]*N4+log2[(tric>>N2)&MASK]*N2+log2[(tric>>(2*N2))&MASK]]=G;
                G++;
            }
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
        CTARGET=compress(TARGET);

        int FULL_GROUP_SIZE=9;
        ArrMap[] minorGroupMaps=new ArrMap[FULL_GROUP_SIZE];
        for (int sz=1; sz<FULL_GROUP_SIZE; sz++) minorGroupMaps[sz]=new MapArrMap(); {
            long st=System.currentTimeMillis();
            long work=0;
            int[] symmGroupSzHist=new int[FULL_GROUP_SIZE];
            boolean[] taken=new boolean[1<<(3*N2)];
            for (int xc=1; xc<(1<<N2); xc++) for (int yc=1; yc<(1<<N2); yc++) for (int zc=1; zc<(1<<N2); zc++) {
                int tri_code=xc|(yc<<N2)|(zc<<(2*N2));
                if (!taken[tri_code]) {
                    int[] transformed_tri_codes=tri_group_codes(xc,yc,zc);
                    for (int c:transformed_tri_codes) taken[c]=true;
                    int S=transformed_tri_codes.length;
                    if (S<FULL_GROUP_SIZE) {
                        int[] ret=compress(sumdecomp(tricodes2trimats(transformed_tri_codes)));
                        if (minorGroupMaps[S].get(ret)==null) {
                            symmGroupSzHist[S]++;
                            minorGroupMaps[S].put(ret,new int[][] {{tri_code}});
                        }
                    }
                    work++;
                }
            }
            System.out.printf("%d %d %s%n",work,System.currentTimeMillis()-st,Arrays.toString(symmGroupSzHist));
        }

        //TODO: TRY CYC3+ALLPERM?????!!!!!

        System.out.println("generating minor map");
        minorGroupTensors=new ArrayList<>();
        minorGroupSizes=new ArrayList<>();
        for (int S=1; S<FULL_GROUP_SIZE; S++)
            for (int[] K:minorGroupMaps[S].keys()) {
                minorGroupTensors.add(K);
                minorGroupSizes.add(S);
            }
        nMinor=minorGroupTensors.size();
        System.out.println(nMinor+" total minor groups");

        MAX_Rminor=23-9*R;
        System.out.println("MAX_Rminor="+MAX_Rminor);
        minorMap=new BinaryTrieArrMap();
        dfs_info=new ArrayList<>();
        TIME_ST=System.currentTimeMillis(); TIME_MARK=0;
        dfs_work=0;
        generateMinorMap(new int[G],0,0);
        System.out.printf("%d %d %d%n",System.currentTimeMillis()-TIME_ST,dfs_work,minorMap.size());

        List<Integer> sparseTrimatCodes=new ArrayList<>();
        List<int[]> sparseTrimatTensors=new ArrayList<>(); {
            boolean[] taken=new boolean[1<<(3*N2)];
            int[] bitcnt=new int[1<<N2];
            bitcnt[0]=0;
            for (int i=1; i<(1<<N2); i++) bitcnt[i]=bitcnt[i/2]+i%2;
            for (int a=1; a<(1<<N2); a++) if (bitcnt[a]<=MAXNZ)
                for (int b=1; b<(1<<N2); b++) if (bitcnt[a]*bitcnt[b]<=MAXNZ)
                    for (int c=1; c<(1<<N2); c++) if (bitcnt[a]*bitcnt[b]*bitcnt[c]<=MAXNZ) {
                        int tricode=a|(b<<N2)|(c<<(2*N2));
                        if (!taken[tricode]) {
                            int[] codes=tri_group_codes(a,b,c);
                            for (int code:codes) taken[code]=true;
                            sparseTrimatCodes.add(tricode);
                            sparseTrimatTensors.add(compress(sumdecomp(tricodes2trimats(codes))));
                        }
                    }
            System.out.println(sparseTrimatCodes.size()+" sparse matrix triplets");
            System.out.println("current heap usage="+Runtime.getRuntime().totalMemory());
        }

        System.out.println("searching");
        long[] histogram=new long[MAXDIST+1];
        long st=System.currentTimeMillis(), mark=0;
        int bscr=Integer.MAX_VALUE;
        long work=0; search_work=0;
        if (R==2) {
            for (int ia=0; ia<sparseTrimatCodes.size(); ia++)
                for (int ib=0; ib<=ia; ib++) {
                    long time=System.currentTimeMillis()-st;
                    if (time>=mark) {
                        mark+=1000_000;
                        System.out.printf("%d %d %d%n",work,search_work,time);
                    }
                    work++;
                    int[] CT=sum(sparseTrimatTensors.get(ia),sparseTrimatTensors.get(ib));
                    int[][] aCT=Searcher.closestWithin(minorMap,CT,MAXDIST);
                    if (aCT[0]!=null) {
                        int scr=aCT[1][0];
                        histogram[scr]++;
                        if (scr<bscr) {
                            bscr=scr;
                            System.out.println("scr="+scr);
                            System.out.println("minor:");
                            for (int i:minorMap.get(aCT[0])[0])
                                System.out.println(trimat2str(bin2trimat(
                                        minorGroupMaps[minorGroupSizes.get(i)].get(minorGroupTensors.get(i))[0][0]
                                )));
                            System.out.println("major:");
                            for (int code:new int[] {sparseTrimatCodes.get(ia),sparseTrimatCodes.get(ib)})
                                System.out.println(trimat2str(bin2trimat(code)));
                        }
                    }
                }
            System.out.printf("%d %d %d%n",work,search_work,System.currentTimeMillis()-st);
            System.out.println("histogram="+Arrays.toString(histogram));
        }

    }
}
