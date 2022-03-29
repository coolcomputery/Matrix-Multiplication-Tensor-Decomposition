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
    private static int[] listSum(int[] A, int[] B) {
        if (A.length!=B.length) throw new RuntimeException();
        int[] C=new int[A.length];
        for (int i=0; i<A.length; i++) C[i]=A[i]+B[i];
        return C;
    }

    static long ncombos(int n, int k) {
        if (n<k) return 0;
        long out=1;
        for (int i=n; i>n-k; i--) out*=i;
        for (int i=1; i<=k; i++) out/=i;
        return out;
    }
    static int[] idx2combo(int N, int K, long idx) {
        if (idx<0 || idx>=ncombos(N,K)) return null;
        int[] out=new int[K];
        for (int ki=0; ki<K; ki++) {
            int k=K-ki, l=ki==0?0:out[ki-1]+1;
            long tot=ncombos(N-l,k), F=tot-idx;
            //find smallest n s.t. ncombos(n,k)>=F
            //(n-k)^k/(k!) <= ncombos(n,k) <= n^k/(k!)
            //--> optimal n between floor( (f*k!)^(1/k) ) and ceil( (f*k!)^(1/k)+k )
            int kfac=1; for (int i=1; i<=k; i++) kfac*=i;
            double approx=Math.pow(F*kfac,1.0/k);
            int lo=Math.max(1,(int)approx), hi=Math.min(N-l,(int)Math.ceil(approx)+k);
            while (lo<hi) {
                int mi=(lo+hi)/2;
                if (ncombos(mi,k)<F) lo=mi+1;
                else hi=mi;
            }
            out[ki]=N-lo;
            idx-=tot-ncombos(lo,k);
        }
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

    static class BeamSearch {
        int[][] A; BigInteger[] C;
        int N, S;
        BigInteger cost(boolean[] set) {
            BigInteger out=BigInteger.ZERO;
            for (int c=0; c<N; c++) if (set[c]) out=out.add(C[c]);
            return out;
        }
        BigInteger scr(boolean[][][] minors) {
            BigInteger out=BigInteger.ZERO;
            for (boolean[][] minor:minors)
                out=out.add(cost(minor[0])).add(cost(minor[1]));
            return out;
        }
        boolean[][][] bminors; BigInteger bscr;
        class Sol implements Comparable<Sol> {
            boolean[][][] minors;
            BigInteger scr;
            Sol() {
                minors=new boolean[S][2][N];
                scr=BigInteger.ZERO;
            }
            boolean contains(int v) {
                for (boolean[][] minor:minors)
                    for (int r=0; r<N; r++) if (minor[0][r])
                        for (int c=0; c<N; c++) if (minor[1][c])
                            if (A[r][c]==v) return true;
                return false;
            }
            Sol add(int[] l, int g) {
                boolean[][][] nminors=new boolean[S][][];
                for (int s=0; s<S; s++) nminors[s]=new boolean[][] {Arrays.copyOf(minors[s][0],N),Arrays.copyOf(minors[s][1],N)};
                nminors[g][0][l[0]]=true;
                nminors[g][1][l[1]]=true;
                BigInteger nscr=scr.add(minors[g][0][l[0]]?BigInteger.ZERO:C[l[0]]).add(minors[g][1][l[1]]?BigInteger.ZERO:C[l[1]]);
                Sol out=new Sol();
                out.minors=nminors;
                out.scr=nscr;
                return out;
            }
            public int compareTo(Sol s) {
                return scr.compareTo(s.scr);
            }
        }
        class Mod implements Comparable<Mod> {
            int[] l; int g, i;
            BigInteger scr;
            Mod(int[] l, int g, int i, BigInteger scr) {
                this.l=l; this.g=g; this.i=i; this.scr=scr;
            }
            public int compareTo(Mod o) {
                return scr.compareTo(o.scr);
            }
        }
        BeamSearch(int[][] A, BigInteger[] C, int S, BigInteger MAXTOTROW) {
            N=A.length;
            this.A=A; this.C=C; this.S=S;
            List<List<int[]>> locs=new ArrayList<>();
            for (int i=0; i<N; i++) locs.add(new ArrayList<>());
            for (int r=0; r<N; r++) if (C[r].compareTo(MAXTOTROW)<=0) for (int c=0; c<N; c++) if (A[r][c]>-1)
                locs.get(A[r][c]).add(new int[] {r,c});

            long st=System.currentTimeMillis();
            List<Sol> sols=new ArrayList<>(Collections.singletonList(new Sol()));
            int BEAMLIM=10000;
            for (int v=N-1; v>-1; v--) { //for some reason, going backwards produces a much better result than going forwards
                List<Mod> mods=new ArrayList<>();
                for (int i=0; i<sols.size(); i++) {
                    Sol sol=sols.get(i);
                    if (sol.contains(v)) mods.add(new Mod(null,-1,i,sol.scr));
                    else {
                        for (int[] l:locs.get(v)) {
                            for (int g=0; g<S; g++) {
                                BigInteger nscr=sol.scr.add(sol.minors[g][0][l[0]]?BigInteger.ZERO:C[l[0]])
                                        .add(sol.minors[g][1][l[1]]?BigInteger.ZERO:C[l[1]]);
                                boolean[] minorr=sol.minors[g][0];
                                if (minorr[l[0]] || (cost(minorr).add(C[l[0]])).compareTo(MAXTOTROW)<=0)
                                    mods.add(new Mod(l,g,i,nscr));
                            }
                        }
                    }
                }
                Collections.sort(mods);
                List<Sol> nsols=new ArrayList<>();
                for (int mi=0; mi<Math.min(mods.size(),BEAMLIM); mi++) {
                    Mod m=mods.get(mi);
                    Sol sol=sols.get(m.i);
                    nsols.add(m.l==null?sol:sol.add(m.l,m.g));
                }
                sols=nsols;
            }
            bminors=sols.get(0).minors;
            bscr=scr(bminors);
            if (bscr.compareTo(sols.get(0).scr)!=0) throw new RuntimeException();
            System.out.println("time="+(System.currentTimeMillis()-st));
        }
    }

    public static int compareTensors(int[] t0, int[] t1) {
        for (int i=t0.length-1; i>0; i--) if (t0[i]!=t1[i]) return Integer.compare(t0[i],t1[i]);
        return Integer.compare(t0[0],t1[0]);
    }
    private abstract static class GroupMerger {
        //group a set of ints by G(e), where each int e represents a tensor T(e)
        //0<=e<E; if G(e)=-1, we should discard that e; otherwise, G(e)>=0
        //then within each group, if multiple e represent the same tensor T(e), only keep the one with lowest s(e),
        //  for some given function s ("score")
        //we are given that 0<=
        abstract int group(int e);
        abstract int[] tensor(int e);
        abstract int score(int e);
        int[][] ret(int E, int G) {
            long st=System.currentTimeMillis(), mark=0;
            int[] groupId=new int[E], groupFreq=new int[G]; Arrays.fill(groupId,-1);
            System.out.println("calculating group numbers:");
            for (int e=0; e<E; e++) {
                if ((e%127)==0) {
                    long time=System.currentTimeMillis()-st;
                    if (time>=mark) {
                        if (mark>0) System.out.println("cnt="+e+" t="+time+" m="+usedMem());
                        mark+=10_000;
                    }
                }
                int g=group(e);
                if (g>-1) {
                    groupId[e]=g;
                    groupFreq[g]++;
                }
            }
            System.out.println("t="+(System.currentTimeMillis()-st)+" m="+usedMem());

            int[][] groups=new int[G][];
            for (int g=0; g<G; g++) if (groupFreq[g]>0) groups[g]=new int[groupFreq[g]];
            Arrays.fill(groupFreq,0);
            for (int e=0; e<E; e++) {
                if ((e%127)==0) {
                    long time=System.currentTimeMillis()-st;
                    if (time>=mark) {
                        if (mark>0) System.out.println("cnt="+e+" t="+time+" m="+usedMem());
                        mark+=10_000;
                    }
                }
                int g=groupId[e];
                if (g>-1) {
                    if (groups[g]==null) throw new RuntimeException(g+"");
                    groups[g][groupFreq[g]++]=e;
                }
            }
            System.out.println("grouping time="+(System.currentTimeMillis()-st));

            st=System.currentTimeMillis();
            int[][] out=new int[G][];
            for (int g=0; g<G; g++) if (groups[g]!=null) {
                int[] elems=groups[g]; int sz=elems.length;
                int[][] tensors=new int[sz][];;
                for (int i=0; i<sz; i++) {
                    int e=elems[i];
                    tensors[i]=tensor(e);
                }
                Integer[] idxs=new Integer[sz]; for (int i=0; i<sz; i++) idxs[i]=i;
                Arrays.sort(idxs,new Comparator<Integer>() {
                    public int compare(Integer o1, Integer o2) {
                        int d=compareTensors(tensors[o1],tensors[o2]);
                        return d==0?Integer.compare(score(elems[o1]),score(elems[o2])):d;
                    }
                });
                int[] merged=new int[sz]; int n=0;
                for (int i=0; i<sz;) {
                    merged[n++]=elems[idxs[i]];
                    int j=i; while (j<sz && Arrays.equals(tensors[idxs[i]],tensors[idxs[j]])) j++;
                    i=j;
                }
                out[g]=Arrays.copyOf(merged,n);
            }
            System.out.println("merging time="+(System.currentTimeMillis()-st));
            return out;
        }
    }

    public static void main(String[] args) {
        long START=System.currentTimeMillis();
        System.out.println("max heap size="+Runtime.getRuntime().maxMemory());
        System.out.println("m="+memStats());

        N=3;
        N2=N*N; N4=N2*N2; N6=N4*N2;

        int MAX_R=22, MAX_Z=12; String MODE="FLIP";
        System.out.printf("N=%d MAX_R=%d MAX_Z=%d MODE=%s%n",N,MAX_R,MAX_Z,MODE);

        BigInteger MEM_LIMIT=new BigInteger(""+1000_000_000);
        System.out.printf("MEM_LIMIT=%d%n",MEM_LIMIT);

        int[] TARGET=new int[N6];
        for (int i=0; i<N; i++) for (int j=0; j<N; j++) for (int k=0; k<N; k++)
            TARGET[(i*N+j)*N2+(j*N+k)]|=1<<(k*N+i);
        MASK=(1<<N2)-1;

        //generate the set of transformation functions that will be used to enforce symmetry
        {
            List<int[]> perms;
            switch (MODE) {
                case "CYCLIC":
                    perms=new ArrayList<>(); {
                        int[] p=new int[N]; for (int i=0; i<N; i++) p[i]=i;
                        perms.add(p);
                    }
                    break;
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
        System.out.println("MAJOR_GROUP_SIZE="+MAJOR_GROUP_SIZE);

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
            Gd32=(G-1)/32+1;
            System.out.println("G="+G);
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
        int[] groupSize=new int[1<<(3*N2)]; Arrays.fill(groupSize,-1);
        int[][] triplets; {
            System.out.println("generating groups");
            int[] bitcnt=new int[1<<N2]; bitcnt[0]=0; for (int i=1; i<(1<<N2); i++) bitcnt[i]=bitcnt[i/2]+i%2;
            int[] groupSzHist=new int[MAJOR_GROUP_SIZE+1];
            boolean[] taken=new boolean[1<<(3*N2)];
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
                    if (bitcnt[a]*bitcnt[b]*bitcnt[c]<=MAX_Z) {
                        groupSzHist[S]++;
                        groupSize[triplet]=S;
                        int[] eval=symmCompress(xortensor(triGroup));
                        groupTensor[triplet]=eval;
                    }
                    work++;
                }
            }
            System.out.printf("work=%d t=%d m=%s histogram of sizes=%s end%n",
                    work,System.currentTimeMillis()-st,memStats(),Arrays.toString(groupSzHist));
            triplets=new GroupMerger() {
                int group(int e) { return groupSize[e]; }
                int[] tensor(int e) { return groupTensor[e]; };
                int score(int e) { return e; }
            }.ret(1<<(3*N2),MAJOR_GROUP_SIZE+1);
            for (int r=1; r<=MAJOR_GROUP_SIZE; r++) if (triplets[r]==null) triplets[r]=new int[] {};
        }
        System.out.println("m="+memStats());


        int[] triCnts=new int[MAJOR_GROUP_SIZE+1];
        for (int r=1; r<=MAJOR_GROUP_SIZE; r++) triCnts[r]=triplets[r].length;
        System.out.println(Arrays.toString(triCnts));

        class Profiles {
            List<int[]> out;
            int[] limits;
            int[] freq;
            int maxTot;
            void dfs(int rankLeft, int m) {
                if (m==0) {
                    out.add(Arrays.copyOf(freq,freq.length));
                    return;
                }
                for (int cnt=0; rankLeft-cnt*m>=0 && cnt<=limits[m]; cnt++) {
                    freq[m]=cnt;
                    dfs(rankLeft-cnt*m,m-1);
                }
            }
            List<int[]> generate(int maxTot, int[] limits) {
                this.maxTot=maxTot; this.limits=limits;
                out=new ArrayList<>();
                freq=new int[limits.length];
                dfs(maxTot,limits.length-1);
                return out;
            }
        }
        List<int[]> profiles=new Profiles().generate(MAX_R,triCnts);
        int nP=profiles.size();
        System.out.println("# profiles="+nP);

        class ProfileCost {
            private static BigInteger nCr(int n, int k) {
                if (n<k) return BigInteger.ZERO;
                BigInteger out=BigInteger.ONE;
                for (int i=n; i>n-k; i--) out=out.multiply(new BigInteger(i+""));
                for (int i=1; i<=k; i++) out=out.divide(new BigInteger(i+""));
                return out;
            }
            BigInteger cost(int[] p) {
                BigInteger n=BigInteger.ONE;
                for (int r=1; r<=MAJOR_GROUP_SIZE; r++) n=n.multiply(nCr(triCnts[r],p[r]));
                return n;
            }
            BigInteger cost(List<int[]> P) {
                BigInteger out=BigInteger.ZERO;
                for (int[] p:P) out=out.add(cost(p));
                return out;
            }
        } ProfileCost PROFILECOST=new ProfileCost();

        System.out.println("size of entire search space="+PROFILECOST.cost(profiles));

        List<List<int[]>> P0s=new ArrayList<>(), P1s=new ArrayList<>(); {
            int[][] table=new int[nP][nP]; {
                Map<String,Integer> profile2id=new HashMap<>();
                for (int pi=0; pi<nP; pi++) profile2id.put(Arrays.toString(profiles.get(pi)),pi);
                for (int pi=0; pi<nP; pi++) for (int pj=0; pj<nP; pj++)
                    table[pi][pj]=profile2id.getOrDefault(Arrays.toString(listSum(profiles.get(pi),profiles.get(pj))),-1);
            }
            BigInteger[] costs=new BigInteger[nP];
            for (int pi=0; pi<nP; pi++) costs[pi]=PROFILECOST.cost(profiles.get(pi));

            System.out.println("beam search");
            boolean[][][] bsol=null;
            BigInteger pscr=null;
            for (int S=1; S<=N; S++) {
                BeamSearch $=new BeamSearch(table,costs,S,MEM_LIMIT);
                System.out.println(S+" "+$.bscr);
                if (pscr!=null && pscr.compareTo($.bscr)<=0) break;
                else {
                    pscr=$.bscr;
                    bsol=$.bminors;
                }
            }

            System.out.println("totCost="+pscr);
            for (boolean[][] m:bsol) {
                List<int[]> P0=new ArrayList<>(), P1=new ArrayList<>();
                for (int p=0; p<nP; p++) if (m[0][p]) P0.add(profiles.get(p));
                for (int p=0; p<nP; p++) if (m[1][p]) P1.add(profiles.get(p));
                System.out.print("map "); for (int[] p:P0) System.out.print(" "+Arrays.toString(p)); System.out.println();
                System.out.print("iter"); for (int[] p:P1) System.out.print(" "+Arrays.toString(p)); System.out.println();
                P0s.add(P0); P1s.add(P1);
                System.out.println(PROFILECOST.cost(P0)+" "+PROFILECOST.cost(P1));
            }
            //check validity
            Set<String> prod=new HashSet<>();
            for (int s=0; s<P0s.size(); s++)
                for (int[] p0:P0s.get(s)) for (int[] p1:P1s.get(s))
                    prod.add(Arrays.toString(listSum(p0,p1)));
            for (int[] p:profiles) if (!prod.contains(Arrays.toString(p))) throw new RuntimeException("Product does not contain "+Arrays.toString(p));
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
        class TrisInfo {
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
        } TrisInfo $=new TrisInfo();

        class D0Set {
            //converts set of matrix triplets to int
            List<int[]> P0;
            int[] amts;
            int[] tris(int e) {
                int pi=0;
                for (; pi<P0.size(); pi++) {
                    if (e>=amts[pi]) e-=amts[pi];
                    else break;
                }
                int[] p=P0.get(pi);
                List<Integer> out=new ArrayList<>();
                for (int r=MAJOR_GROUP_SIZE; r>=1; r--) {
                    int ncr=(int)ncombos(triCnts[r],p[r]);
                    for (int trii:idx2combo(triCnts[r],p[r],e%ncr))
                        out.add(triplets[r][trii]);
                    e/=ncr;
                }
                return toArr(out);
            }
            //stores a range of integers [0,R), where each integer e has an implicit associated array key(e)
            //when querying for a specific key: if key does not exist, return -1
            long searches, binSearches, binWork;
            long[] filterPassed;
            private long[][] filters;
            //works even though int is signed, because >>> will rotate the signed bit
            private void add(long[] filter, int v) {
                filter[v>>>6]|=1L<<(v&63);
            }
            private long bit(long[] filter, int v) {
                return filter[v>>>6]&(1L<<(v&63));
            }
            private int H=10000019;
            private int[][] chains;
            private int hash(int[] key) {
                int out=0;
                for (int v:key) out^=v;
                return ((out%H)+H)%H;
            }
            public D0Set(List<int[]> P0) {
                this.P0=P0;
                amts=new int[P0.size()];
                for (int pi=0; pi<P0.size(); pi++)
                    amts[pi]=PROFILECOST.cost(P0.get(pi)).intValue();

                int totCombos=0;
                for (int[] p:P0) totCombos+=PROFILECOST.cost(p).intValue();
                long st=System.currentTimeMillis();
                chains=new GroupMerger() {
                    int group(int e) { return hash(tensor(e)); }
                    int[] tensor(int e) { return $.tris2tensor(tris(e)); }
                    int score(int e) { return $.totrank(tris(e)); }
                }.ret(totCombos,H);

                st=System.currentTimeMillis();
                filters=new long[Gd32][1<<26];
                filterPassed=new long[Gd32];
                for (int[] ch:chains) if (ch!=null) for (int e:ch) {
                    int[] K=$.tris2tensor(tris(e));
                    for (int f=0; f<Gd32; f++) add(filters[f],K[f]);
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
                    if (compareTensors(K,$.tris2tensor(tris(elems[mi])))<=0) hi=mi;
                    else lo=mi+1;
                }
                return Arrays.equals(K,$.tris2tensor(tris(elems[lo])))?elems[lo]:-1;
            }
            public int getXorOf(int[] Ka, int[] Kb) {
                searches++;
                for (int f=0; f<Gd32; f++) {
                    if (bit(filters[f],Ka[f]^Kb[f])==0) return -1;
                    filterPassed[f]++;
                }
                int[] K=xor(Ka,Kb);
                return binsearch(chains[hash(K)],K);
            }
        }

        System.out.println("searching m="+memStats());
        int[] CTARGET=symmCompress(TARGET);
        BigInteger tot; {
            BigInteger tmp=BigInteger.ZERO; for (List<int[]> P1:P1s) tmp=tmp.add(PROFILECOST.cost(P1));
            tot=tmp;
        }
        String statsString="%3f%% %3f%% searches=%d filterPassed=%s binSearches=%d binWork=%d t=%d total_t=%d m=%s%n";
        long search_st=System.currentTimeMillis();
        final long[] searches0={0};
        final int[] brank={Integer.MAX_VALUE};
        class Tester {
            String str(int[]... triss) {
                StringBuilder s=new StringBuilder();
                for (int[] combo:triss) {
                    for (int tri:combo) {
                        for (int m:new int[] {tri&MASK,(tri>>N2)&MASK,(tri>>(2*N2))&MASK}) {
                            int[] A=new int[N2]; for (int i=0; i<N2; i++) A[i]=(m>>i)&1;
                            s.append(Arrays.toString(A)).append(",");
                        }
                        s.append("  ");
                    }
                    s.append("\n");
                }
                return s.toString();
            }
            void testSolution(int[]... triss) {
                int[] tensor=new int[Gd32];
                for (int[] tris:triss) for (int tri:tris) tensor=xor(tensor,groupTensor[tri]);
                if (!Arrays.equals(CTARGET,tensor)) throw new RuntimeException("Invalid decomposition of MM tensor:\n"+str(triss));
                int rank=0;
                for (int[] tris:triss) rank+=$.totrank(tris);
                if (rank<brank[0]) {
                    brank[0]=rank;
                    System.out.println("rank="+rank+" generated from\n"+str(triss));
                }
            }
        } Tester TESTER=new Tester();

        for (int s=0; s<P0s.size(); s++) {
            System.out.println("group # "+s);
            List<int[]> P0=P0s.get(s), P1=P1s.get(s);
            D0Set D0=new D0Set(P0); {
                System.out.println("checking decomp<-->int conversion");
                long st=System.currentTimeMillis(); final long[] mark={0};
                int[] idx={0};
                for (int[] p:P0) new ForEachSetOfProfile(p) { void process(int[] tris, int[] tensor) {
                    long time=System.currentTimeMillis()-st;
                    if (time>=mark[0]) {
                        mark[0]+=10_000;
                        System.out.printf("cnt=%d t=%d%n",idx[0],time);
                    }
                    int[] generated=D0.tris(idx[0]); Arrays.sort(generated);
                    int[] tmpTris=Arrays.copyOf(tris,tris.length); Arrays.sort(tmpTris);
                    if (!Arrays.equals(tmpTris,generated)) throw new RuntimeException("tris="+Arrays.toString(tris)+" generated="+Arrays.toString(generated));
                    idx[0]++;
                }};
                System.out.printf("cnt=%d t=%d m=%s%n",idx[0],System.currentTimeMillis()-st,memStats());
            }
            for (int pi=0; pi<P1.size(); pi++) {
                int[] p1=P1.get(pi);
                D0.searches=0; Arrays.fill(D0.filterPassed,0); D0.binSearches=0; D0.binWork=0;
                BigInteger p1tot=PROFILECOST.cost(p1);
                System.out.printf("%d/%d %s expected # searches=%d%n",pi,P1.size(),Arrays.toString(p1),p1tot);
                int firstRank; {
                    int tmp=-1;
                    for (int r=0; r<=MAJOR_GROUP_SIZE; r++) if (p1[r]>0) { tmp=r; break; }
                    firstRank=tmp;
                }
                long st=System.currentTimeMillis(); final long[] mark={0};
                if (firstRank==-1) {
                    int e=D0.getXorOf(CTARGET,new int[Gd32]);
                    if (e>=0) TESTER.testSolution(D0.tris(e));
                }
                else {
                    int[] subp1=Arrays.copyOf(p1,MAJOR_GROUP_SIZE+1);
                    subp1[firstRank]--;
                    long[] iters={0};
                    new ForEachSetOfProfile(subp1) {
                        void process(int[] stris1, int[] stensor1) {
                            if ((iters[0]&127)==0) {
                                long time=System.currentTimeMillis()-st;
                                if (time>=mark[0]) {
                                    if (mark[0]>0) System.out.printf(statsString,(D0.searches+searches0[0])/tot.doubleValue()*100,D0.searches/p1tot.doubleValue()*100,
                                            D0.searches,Arrays.toString(D0.filterPassed),D0.binSearches,D0.binWork,time,System.currentTimeMillis()-search_st,memStats());
                                    mark[0]+=(mark[0]<100_000?10_000:100_000);
                                }
                            }
                            iters[0]++;
                            if (!Arrays.equals($.tris2tensor(stris1),stensor1)) throw new RuntimeException();
                            int[] tmptensor=xor(CTARGET,stensor1);
                            int maxIdx=(idxs.length==0 || subp1[firstRank]==0?triplets[firstRank].length:idxs[0]);
                            for (int idx=0; idx<maxIdx; idx++) {
                                int firstTri=triplets[firstRank][idx];
                                int e=D0.getXorOf(tmptensor,groupTensor[firstTri]);
                                if (e>=0) {
                                    int[] tris1=Arrays.copyOf(stris1,stris1.length+1);
                                    tris1[stris1.length]=firstTri;
                                    TESTER.testSolution(D0.tris(e),tris1);
                                }
                            }
                        }
                    };
                }
                System.out.printf(statsString,(D0.searches+searches0[0])/tot.doubleValue()*100,D0.searches/p1tot.doubleValue()*100,
                        D0.searches,Arrays.toString(D0.filterPassed),D0.binSearches,D0.binWork,System.currentTimeMillis()-st,System.currentTimeMillis()-search_st,memStats());
                searches0[0]+=D0.searches;
            }
        }
        System.out.println("TOTAL TIME="+(System.currentTimeMillis()-START));
    }
}
