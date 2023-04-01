import java.math.BigInteger;
import java.util.*;
public class SymmetricMod2 {
    public static boolean DP_match(OrbitCollection ORBITINFO, int MAXR, int B) {
        System.out.print("\tB="+B);
        if (B>=32 || B>ORBITINFO.BITLEN) throw new RuntimeException();
        //E(h,z)=1 if there is an orbit with tensor_valuation[:B]=h, rank=z; else 0
        //E(h,0)=0 for all h
        long dp_st=System.currentTimeMillis();
        int[][] headsAt; {
            boolean[][] exists=new boolean[MAXR+1][1<<B];
            for (int oi=0; oi<ORBITINFO.NORBITS; oi++) {
                int z=ORBITINFO.ORANKs[oi];
                if (z<=MAXR) exists[z][ORBITINFO.ohead(oi,B)]=true;
            }
            headsAt=new int[MAXR+1][];
            for (int z=1; z<=MAXR; z++) headsAt[z]=ArrayHelp.idxsAt(exists[z]);
            System.out.printf(" head_hist=%s head_time=%d",ArrayHelp.inta2msetstr(ArrayHelp.lengths(headsAt)),System.currentTimeMillis()-dp_st);
        }
        int TARGET_HEAD=ORBITINFO.targethead(B);
        boolean[][] dp=new boolean[MAXR+1][1<<B];
        //dp[z][b]=(there exists a seq. of orbit idx.s Q s.t. sum_k OSIZEs[Q[k]] == z and (eltwise-xor)_k OVECs[Q[k]][:B] == b)
        Arrays.fill(dp[0],false);
        dp[0][0]=true;
        System.out.print(" dp_hist=[");
        if (dp[0][TARGET_HEAD]) {
            System.out.println("] dp_time="+(System.currentTimeMillis()-dp_st));
            return true;
        }
        System.out.print(1);
        for (int z=1; z<=MAXR; z++) {
            for (int lz=1; lz<=MAXR && lz<=z; lz++)
                for (int lh:headsAt[lz]) if (dp[z-lz][TARGET_HEAD^lh]) {
                    System.out.println("] dp_time="+(System.currentTimeMillis()-dp_st));
                    return true;
                }
            Arrays.fill(dp[z],false);
            for (int z0=0; z0<z; z0++)
                for (int h0=0; h0<(1<<B); h0++) if (dp[z0][h0])
                    for (int h1:headsAt[z-z0])
                        dp[z][h0^h1]=true;
            if (dp[z][TARGET_HEAD]) throw new RuntimeException();
            int cnt=0; for (boolean b:dp[z]) if (b) cnt++;
            System.out.print(","+cnt);
        }
        System.out.println("] dp_time="+(System.currentTimeMillis()-dp_st));
        return false;
    }
    public static int[][] MITM_search(OrbitCollection ORBITINFO, int MAXR, int MEM_LIMIT, long RUN_LIMIT) {
        long TOTST=System.currentTimeMillis();
        System.out.println("searching for MAXR="+MAXR);

        System.out.println("finding MITM scheme");
        ProfileManagement.MITM mitm; {
            ProfileManagement.MITMCalculator MITM_CALC=new ProfileManagement.MITMCalculator(ORBITINFO.CANONICAL_ORANKHIST,MAXR,MEM_LIMIT);
            System.out.println("#profiles="+MITM_CALC.PROFILES.length);
            mitm=MITM_CALC.hill_climb(5000);
            System.out.printf("MITM:%n\tmemset=%s%n\titerset=%s%n",ArrayHelp.intaa2str(mitm.memPs),ArrayHelp.intaa2str(mitm.iterPs));
            MITM_CALC.checkMITM(mitm);
            System.out.printf("~~~ totcost=%d totmemcost=%d%n",mitm.totcost,mitm.memcost);
        }
        if (mitm.totcost.compareTo(new BigInteger(""+RUN_LIMIT))>0) {
            System.out.println("TOO EXPENSIVE: EXITING");
            return null;
        }

        System.out.println("memoization");
        Deck mem; {
            long mem_st=System.currentTimeMillis();
            List<int[]> stem_cards=new ArrayList<>();
            List<int[]> stem_vecs=new ArrayList<>();
            List<Integer> stem_ranks=new ArrayList<>();
            long[] leaves=new long[(int)mitm.memcost.longValue()]; Arrays.fill(leaves,CardParser.NOT_A_PAIR);
            int[] leaf_idx={0};
            for (int[] P:mitm.memPs) {
                new CardDFS(ORBITINFO,P) {
                    void process_stem(int[] stem) {
                        int[] s_card=stem_card();
                        stem_cards.add(s_card);
                        stem_vecs.add(Arrays.copyOf(stem,ORBITINFO.WORDLEN));
                        stem_ranks.add(ORBITINFO.rank(s_card));
                    }
                    void process(int[] stem, int oi) {
                        leaves[leaf_idx[0]++]=oi==OrbitCollection.NOT_ORBITIDX?CardParser.EMPTY_PAIR:( (stem_cards.size()-1)*(long)ORBITINFO.NORBITS+oi );
                    }
                };
            }
            if (leaf_idx[0]!=leaves.length) throw new RuntimeException();
            for (long leaf:leaves) if (leaf<0 && leaf!=CardParser.EMPTY_PAIR) throw new RuntimeException();
            System.out.printf("~~~ #stems=%d collect_time=%d%n",stem_cards.size(),System.currentTimeMillis()-mem_st);

            mem=new Deck(ORBITINFO.BITLEN,leaves,
                    new CardParser(ORBITINFO.WORDLEN) {
                        private int last_oi(long leaf) { if (leaf==CardParser.EMPTY_PAIR) throw new RuntimeException(); else return (int)(leaf%ORBITINFO.NORBITS); }
                        private int stemi(long leaf) { if (leaf==CardParser.EMPTY_PAIR) throw new RuntimeException(); else return (int)(leaf/ORBITINFO.NORBITS); }
                        public int _word(long leaf, int w) { return stem_vecs.get(stemi(leaf))[w] ^ ORBITINFO.oword(last_oi(leaf),w); }
                        public int[] _card(long leaf) {
                            int[] s_c=stem_cards.get(stemi(leaf));
                            int[] out=Arrays.copyOf(s_c,s_c.length+1); out[s_c.length]=last_oi(leaf);
                            return out;
                        }
                        public int _rank(long leaf) { return stem_ranks.get(stemi(leaf))+ORBITINFO.ORANKs[last_oi(leaf)]; }
                    },
                    true
            );
            System.out.printf("~~~ #canonical_mem_cards=%d mem_time=%d%n",mem.ps.length,System.currentTimeMillis()-mem_st);
            mem.check(ORBITINFO);
        }

        long iter_st=System.currentTimeMillis();
        List<int[]> sols=new ArrayList<>();
        for (int[] P:mitm.iterPs) {
            long pcost=ProfileManagement.profileCost(ORBITINFO.CANONICAL_ORANKHIST,P).longValue();
            System.out.printf("P=%s size=%d%n",ArrayHelp.inta2str(P),pcost);
            Arrays.fill(mem.nfailedat,0); mem.ntough=0;
            Logger L$=new Logger() {
                public String extra_info() {
                    return String.format("nfailedat=%s ntough=%d",Arrays.toString(mem.nfailedat).replace(" ",""),mem.ntough);
                }
            };
            new CardDFS(ORBITINFO,P,ORBITINFO.TARGETVEC) {
                void process_stem(int[] stem) {}
                void process(int[] stem, int oi) {
                    L$.incr_work();
                    long p=mem.get(stem,ORBITINFO,oi);
                    if (p!=CardParser.NOT_A_PAIR) {
                        List<Integer> sol=ORBITINFO.reps(mem.code_parser.card(p),card());
                        System.out.println("\tsol "+sol);
                        sols.add(ArrayHelp.list2arr(sol));
                    }
                }
            };
            L$.log();
            if (L$.work!=pcost) throw new RuntimeException();
        }
        System.out.printf("~~~ iter_time=%d%n",System.currentTimeMillis()-iter_st);
        return sols.toArray(new int[0][]);
    }
    public static void main(String[] args) {
        long _st=System.currentTimeMillis();
        int N=3, MAXR=23, MAXB=25, MEM_LIMIT=500_000_000; long RUN_LIMIT=500_000_000_000L;
        System.out.printf("N=%d MAXR=%d MAXB=%d MEM_LIMIT=%d RUN_LIMIT=%d%n",N,MAXR,MAXB,MEM_LIMIT,RUN_LIMIT);
        for (String symm_set:args) {
            long st=System.currentTimeMillis();
            OrbitCollection ORBITINFO=new OrbitCollection(N,symm_set);
            int minB=-1; {
                System.out.println("prefix DP:");
                long dp_st=System.currentTimeMillis();
                for (int B=1; B<=MAXB && B<=ORBITINFO.BITLEN && minB==-1; B++)
                    if (!DP_match(ORBITINFO,MAXR,B)) minB=B;
                System.out.printf("~~~ minB=%s dp_time=%d%n",minB==-1?"?":(""+minB),System.currentTimeMillis()-dp_st);
            }
            if (minB==-1) {
                //repeatedly decrease R if needed so that search becomes feasible;
                // then do search for R, and then also do search for R-1 (if R>=1) before stopping
                boolean result_known=false;
                for (int R=MAXR; R>=1; R--) {
                    int[][] sols=MITM_search(ORBITINFO,R,MEM_LIMIT,RUN_LIMIT);
                    if (sols!=null) System.out.printf("~~~ SOLS%d=%s%n",R,ArrayHelp.intaa2str(sols));
                    if (result_known) break;
                    if (sols!=null) result_known=true;
                }
            }
            else System.out.printf("~~~ SOLS%d=%n",MAXR);
            System.out.printf("~~~ tot_time=%d%n",System.currentTimeMillis()-st);
        }
        System.out.println("TOTAL_TIME="+(System.currentTimeMillis()-_st));
    }
}

class ArrayHelp {
    public static String inta2str(int[] A) { return Arrays.toString(A).replace(" ",""); }
    public static String intaa2str(int[][] A) {
        StringBuilder s=new StringBuilder();
        for (int i=0; i<A.length; i++) s.append(i>0?";":"").append(inta2str(A[i]));
        return s.toString();
    }
    public static String inta2msetstr(int[] A) {
        StringBuilder s=new StringBuilder();
        for (int k=0; k<A.length; k++) if (A[k]>0)
            s.append(s.length()>0?",":"").append(k).append(":").append(A[k]);
        return "{"+s+"}";
    }
    public static int[] range(int n) {
        int[] out=new int[n]; for (int i=0; i<n; i++) out[i]=i;
        return out;
    }
    public static int[] list2arr(List<Integer> L) {
        int[] A=new int[L.size()]; for (int i=0; i<A.length; i++) A[i]=L.get(i);
        return A;
    }
    public static String bitvec2str(int[] vec, int F) {
        StringBuilder s=new StringBuilder();
        for (int f=0; f<F; f++) s.append((vec[f/32]>>>(f%32))&1);
        return s.toString();
    }
    public static int[] lengths(int[][] Ls) {
        int[] out=new int[Ls.length];
        for (int i=0; i<Ls.length; i++) out[i]=Ls[i]==null?0:Ls[i].length;
        return out;
    }
    public static int[] idxsAt(boolean[] B) {
        int cnt=0; for (boolean b:B) if (b) cnt++;
        int[] out=new int[cnt];
        for (int i=0, idx=0; i<B.length; i++)
            if (B[i]) out[idx++]=i;
        return out;
    }
}
abstract class Logger {
    long st, mark, work;
    public Logger() {
        st=System.currentTimeMillis(); mark=0; work=0;
    }
    public abstract String extra_info();
    public void log() {
        System.out.printf("\tt=%d work=%d %s%n",System.currentTimeMillis()-st,work,extra_info());
    }
    private void time_log() {
        long tm=System.currentTimeMillis()-st;
        if (tm>=mark) {
            if (mark>0) log();
            while (tm>=mark) mark+=mark<100_000?10_000:mark<1000_000?100_000:1000_000;
        }
    }
    public void incr_work() {
        if (work%128==0) time_log();
        work++;
    }
}

class MatrixHelp {
    public static int bit(int n, int b) { return (n>>>b)&1; }
    public static int[][] transpose(int[][] A) {
        int[][] out=new int[A[0].length][A.length];
        for (int i=0; i<A.length; i++) for (int j=0; j<A[0].length; j++)
            out[j][i]=A[i][j];
        return out;
    }
    private static int[] nullspaceFrees(int[][] A) {
        int R=A.length, C=A[0].length;
        //compute (column-reversed) row echelon form
        List<int[]> leadingElems=new ArrayList<>();
        for (int r0=0, j=C-1; j>=0; j--) {
            int r=r0;
            while (r<R && A[r][j]==0) r++;
            if (r<R) {
                int[] Ar=Arrays.copyOf(A[r],C), Ar0=Arrays.copyOf(A[r0],C);
                A[r]=Ar0; A[r0]=Ar;
                if (A[r0][j]==0) throw new RuntimeException();
                for (int r1=r0+1; r1<R; r1++) if (A[r1][j]==1)
                    for (int c=0; c<C; c++)
                        A[r1][c]^=A[r0][c];
                leadingElems.add(new int[] {r0,j});
                r0++;
            }
        }
        //return free variables
        boolean[] free=new boolean[C]; Arrays.fill(free,true);
        for (int[] e:leadingElems) free[e[1]]=false;
        return ArrayHelp.idxsAt(free);
    }

    int N, N2, N4, N6, NMATS, MATMASK, NTRIPLETS;
    private int[][] PROD;
    private int[] TRANSPOSED, INV;
    public int mat2code(int[][] M) {
        int out=0;
        for (int i=0; i<N2; i++) out|=M[i/N][i%N]<<i;
        return out;
    }
    public int[][] code2mat(int v) {
        int[][] out=new int[N][N];
        for (int i=0; i<N2; i++) out[i/N][i%N]=bit(v,i);
        return out;
    }
    private int[][] binprod(int[][] A, int[][] B) {
        int[][] C=new int[N][N];
        for (int i=0; i<N; i++) for (int j=0; j<N; j++) for (int k=0; k<N; k++)
            C[i][k]^=A[i][j]&B[j][k];
        return C;
    }
    private int matstr2code(String s) {
        if (s.length()!=N2) throw new RuntimeException();
        int out=0;
        for (int i=0; i<N2; i++) {
            int v=s.charAt(i)-'0'; if (v<0 || v>1) throw new RuntimeException();
            out|=v<<i;
        }
        return out;
    }
    public MatrixHelp(int N) {
        this.N=N; N2=N*N; N4=N2*N2; N6=N4*N2;
        NMATS=1<<N2; MATMASK=(1<<N2)-1; NTRIPLETS=NMATS*NMATS*NMATS;
        TRANSPOSED=new int[NMATS];
        int[][][] mats=new int[NMATS][][];
        for (int c=0; c<NMATS; c++) {
            mats[c]=code2mat(c);
            TRANSPOSED[c]=mat2code(transpose(mats[c]));
        }
        PROD=new int[NMATS][NMATS];
        INV=new int[NMATS]; Arrays.fill(INV,-1);
        int cI=0; for (int r=0; r<N; r++) cI|=1<<(r*N+r);
        for (int ca=0; ca<NMATS; ca++) for (int cb=0; cb<NMATS; cb++) {
            PROD[ca][cb]=mat2code(binprod(mats[ca],mats[cb]));
            if (PROD[ca][cb]==cI) INV[ca]=cb;
        }
    }
    public int mats2tri(int a, int b, int c) { return a|(b<<N2)|(c<<(N2*2)); }
    public int tri2matA(int tri) { return tri&MATMASK; }
    public int tri2matB(int tri) { return (tri>>>N2)&MATMASK; }
    public int tri2matC(int tri) { return (tri>>>(2*N2))&MATMASK; }
    public int[] tri2vectensor(int tri) {
        int a=tri2matA(tri), b=tri2matB(tri), c=tri2matC(tri);
        int[] out=new int[N6];
        for (int i=0; i<N2; i++) if (bit(a,i)==1)
            for (int j=0; j<N2; j++) if (bit(b,j)==1)
                for (int k=0; k<N2; k++) if (bit(c,k)==1)
                    out[i*N4+j*N2+k]=1;
        return out;
    }
    public int[] tris2tensortubes(List<Integer> tris) {
        int[] tubes=new int[N4];
        for (int tri:tris) {
            int na=tri2matA(tri), nb=tri2matB(tri), nc=tri2matC(tri);
            for (int i=0; i<N2; i++) if (bit(na,i)==1)
                for (int j=0; j<N2; j++)
                    tubes[i*N2+j]^=bit(nb,j)*nc;
        }
        return tubes;
    }
    public int tensortubes2elem(int[] ttubes, int i) {
        return bit(ttubes[i/N2],i%N2);
    }
    public int[] compressed(int[] ttubes, int[] idxs) {
        int F=idxs.length, W=(F-1)/32+1;
        int[] out=new int[W];
        for (int f=0; f<F; f++) out[f/32]|=tensortubes2elem(ttubes,idxs[f])<<(f%32);
        return out;
    }

    public static int CYC_CODE=-1, TP_CODE=-2;
    public int[] funcstr2funcarr(String tstr) {
        if (tstr.equals("id")) return new int[] {};
        String[] strs=tstr.split("@");
        int[] out=new int[strs.length];
        for (int i=0; i<strs.length; i++) {
            String str=strs[i];
            if (str.equals("cyc")) out[i]=CYC_CODE;
            else if (str.equals("tp")) out[i]=TP_CODE;
            else {
                if (!str.startsWith("tr")) throw new RuntimeException();
                String[] ss=str.substring(2).split("-");
                if (ss.length==3) out[i]=mats2tri(matstr2code(ss[0]),matstr2code(ss[1]),matstr2code(ss[2]));
                else throw new RuntimeException();
            }
        }
        return out;
    }
    public int transformedTriplet(int[] funcs, int tri0) {
        int tri=tri0;
        for (int i=funcs.length-1; i>=0; i--) {
            int f=funcs[i];
            int a=tri2matA(tri), b=tri2matB(tri), c=tri2matC(tri);
            if (f==CYC_CODE) tri=mats2tri(b,c,a);
            else if (f==TP_CODE) tri=mats2tri(TRANSPOSED[c],TRANSPOSED[b],TRANSPOSED[a]);
            else {
                int x=tri2matA(f), y=tri2matB(f), z=tri2matC(f);
                tri=mats2tri(PROD[PROD[x][a]][INV[y]],PROD[PROD[y][b]][INV[z]],PROD[PROD[z][c]][INV[x]]);
            }
        }
        return tri;
    }
    public int[] freeIdxs(int[][] FUNC_CHAINS) {
        List<int[]> M_null=new ArrayList<>();
        for (int[] fc:FUNC_CHAINS) {
            int[][] M=new int[N6][];
            //here, store a N2xN2xN2 tensor T with A s.t. T[a,b,c]=A[a*N4+b*N2+c]
            for (int i=0; i<N2; i++) for (int j=0; j<N2; j++) for (int k=0; k<N2; k++)
                M[i*N4+j*N2+k]=tri2vectensor(transformedTriplet(fc,mats2tri(1<<i,1<<j,1<<k)));
            M=MatrixHelp.transpose(M);
            for (int r=0; r<N6; r++) M[r][r]^=1;
            for (int[] row:M) M_null.add(row);
        }
        return M_null.size()==0?ArrayHelp.range(N6):nullspaceFrees(M_null.toArray(new int[0][]));
    }
}
class OrbitCollection {
    public static final int NOT_ORBITIDX=-1;
    int BITLEN, WORDLEN, RANK_BOUND;
    int[][] OVECs;
    int[] OREPs, ORANKs;
    int NORBITS;
    int[] TARGETVEC;
    int[] CANONICAL_ORANKHIST; int[][] CANONICAL_ORBITS_BY_SIZE;
    private static int lowestBits(int x,int b) { if (b>32) throw new RuntimeException(); if (b==32) return x; return x&((1<<b)-1); }
    public int oword(int oi, int w) { return OVECs[oi][w]; }
    public int ohead(int oi, int b) { return lowestBits(oword(oi,0),b); }
    public int targethead(int b) { return lowestBits(TARGETVEC[0],b); }
    public int xorword(int[] stem, int oi, int w) { if (oi==NOT_ORBITIDX) return stem[w]; return stem[w]^oword(oi,w); }
    public int[] xorvec(int[] stem, int oi) {
        int[] out=new int[WORDLEN];
        for (int w=0; w<WORDLEN; w++) out[w]=xorword(stem,oi,w);
        return out;
    }
    public int[] vec(int[] card) {
        int[] out=new int[WORDLEN];
        for (int oi:card)
            for (int w=0; w<WORDLEN; w++)
                out[w]^=oword(oi,w);
        return out;
    }
    public int rank(int[] card) {
        int out=0;
        for (int oi:card) out+=ORANKs[oi];
        return out;
    }
    public List<Integer> reps(int[]... cards) {
        List<Integer> reps=new ArrayList<>();
        for (int[] card:cards) for (int oi:card) reps.add(OREPs[oi]);
        return reps;
    }
    public OrbitCollection(int N, String SYMM_SET) {
        MatrixHelp $=new MatrixHelp(N);
        if (3*$.N2>32) throw new RuntimeException("Too many bits in a triplet of NxN matrices to fit in a 32-bit int");
        System.out.printf("@@@ transforms=%s%ngenerating matrix triplet orbits:%n",SYMM_SET);
        String[] TRANSFORMS=SYMM_SET.split(",");
        int[][] FUNC_CHAINS=new int[TRANSFORMS.length][]; for (int i=0; i<TRANSFORMS.length; i++) FUNC_CHAINS[i]=$.funcstr2funcarr(TRANSFORMS[i]);
        int[] frees=$.freeIdxs(FUNC_CHAINS);
        System.out.printf("\t#free_idxs=%d free_idxs=%s",frees.length,ArrayHelp.inta2str(frees));
        BITLEN=frees.length; WORDLEN=(BITLEN-1)/32+1;
        //"tube storage": store a N2xN2xN2 tensor T as A s.t. T[a,b,c]=the c-th bit of A[a*N2+b]
        {
            int[] MMT=new int[$.N4];
            for (int i=0; i<N; i++) for (int j=0; j<N; j++) for (int k=0; k<N; k++) MMT[(i*N+j)*$.N2+(j*N+k)]^=1<<(k*N+i);
            TARGETVEC=$.compressed(MMT,frees);
            if (TARGETVEC.length!=WORDLEN) throw new RuntimeException();
            System.out.println("\tcompressed(MMT)="+ArrayHelp.bitvec2str(TARGETVEC,BITLEN));
        }
        List<Integer> reps=new ArrayList<>(), ranks=new ArrayList<>(); List<int[]> vecs=new ArrayList<>();
        { //calculate compressed tensors
            boolean[] seen=new boolean[$.NTRIPLETS];
            int[] nprocessed={0};
            Logger L$=new Logger() {
                public String extra_info() { return String.format("#processed=%d",nprocessed[0]); }
            };
            for (int rep=0; rep<$.NTRIPLETS; rep++)
                if (!seen[rep]) {
                    L$.incr_work();
                    List<Integer> orbit=new ArrayList<>(); //BFS over all possible transformed versions of the triplet
                    orbit.add(rep); seen[rep]=true;
                    for (int i=0; i<orbit.size(); i++) {
                        int tri=orbit.get(i);
                        for (int[] fc:FUNC_CHAINS) {
                            int ntri=$.transformedTriplet(fc,tri);
                            if (!seen[ntri]) {
                                orbit.add(ntri); seen[ntri]=true;
                            }
                        }
                    }
                    int sz=orbit.size();
                    nprocessed[0]+=sz;
                    reps.add(rep);
                    int[] vec=$.compressed($.tris2tensortubes(orbit),frees);
                    if (vec.length!= WORDLEN) throw new RuntimeException();
                    vecs.add(vec);
                    ranks.add(sz);
                }
            L$.log();
            RANK_BOUND=0; for (int r:ranks) RANK_BOUND=Math.max(RANK_BOUND,r);
            RANK_BOUND++;
        }
        OREPs=ArrayHelp.list2arr(reps); OVECs=vecs.toArray(new int[0][]); ORANKs=ArrayHelp.list2arr(ranks);
        NORBITS=OREPs.length;
        int[] hist=new int[RANK_BOUND]; for (int r:ORANKs) hist[r]++;
        System.out.println("~~~ orbit_rank_histogram="+ArrayHelp.inta2msetstr(hist));

        System.out.println("simple orbit elimination:");
        long st=System.currentTimeMillis();
        CardParser singletonCardParser=new CardParser(WORDLEN) {
            public int _word(long oi, int w) { return oword((int)oi,w); }
            public int[] _card(long oi) { return new int[] {(int)oi}; }
            public int _rank(long oi) { return ORANKs[(int)oi]; }
        };
        Deck singleOrbits; {
            long[] ois=new long[NORBITS+1]; for (int i=0; i<NORBITS; i++) ois[i]=i;
            ois[NORBITS]=CardParser.EMPTY_PAIR;
            singleOrbits=new Deck(BITLEN,ois,singletonCardParser,false);
        }
        List<List<Integer>> groupedOis=new ArrayList<>(); for (int z = 0; z< RANK_BOUND; z++) groupedOis.add(new ArrayList<>());
        for (long p:singleOrbits.ps) if (p!=CardParser.EMPTY_PAIR) {
            int oi=(int)p;
            groupedOis.get(ORANKs[oi]).add(oi);
        }
        CANONICAL_ORBITS_BY_SIZE=new int[RANK_BOUND][];
        for (int z = 1; z< RANK_BOUND; z++)
            CANONICAL_ORBITS_BY_SIZE[z]=ArrayHelp.list2arr(groupedOis.get(z));
        CANONICAL_ORANKHIST=ArrayHelp.lengths(CANONICAL_ORBITS_BY_SIZE);
        System.out.printf("~~~ canonical_orbit_rank_histogram=%s canonical_time=%d%n",
                ArrayHelp.inta2msetstr(CANONICAL_ORANKHIST),System.currentTimeMillis()-st);
    }
}

class ProfileManagement {
    public static List<int[]> profiles(int[] H, int MAXR) {
        List<int[]> out=new ArrayList<>();
        class DFS {
            int[] profile=new int[H.length];
            public void dfs(int k, int r) {
                if (k==H.length) {
                    out.add(Arrays.copyOf(profile,H.length));
                    return;
                }
                for (int h=0; r+k*h<=MAXR && h<=H[k]; h++) {
                    profile[k]=h;
                    dfs(k+1,r+k*h);
                }
            }
        } new DFS().dfs(0,0);
        return out;
    }
    public static int[] eltsum(int[] A, int[] B) {
        if (A.length!=B.length) throw new RuntimeException();
        int[] C=new int[A.length];
        for (int i=0; i<A.length; i++) C[i]=A[i]+B[i];
        return C;
    }
    public static BigInteger nCr(int n, int k) {
        BigInteger out=BigInteger.ONE;
        for (int i=0; i<k; i++) out=out.multiply(new BigInteger(""+(n-i)));
        for (int i=1; i<=k; i++) out=out.divide(new BigInteger(""+i));
        return out;
    }
    public static BigInteger profileCost(int[] H, int[] P) {
        if (H.length!=P.length) throw new RuntimeException();
        BigInteger out=BigInteger.ONE;
        for (int i=0; i<H.length; i++) out=out.multiply(nCr(H[i],P[i]));
        return out;
    }
    public static class MITM {
        int[][] memPs, iterPs;
        BigInteger memcost, totcost;
        public MITM(int[][] memPs, int[][] iterPs, BigInteger memcost, BigInteger totcost) {
            this.memPs=memPs; this.iterPs=iterPs; this.memcost=memcost; this.totcost=totcost;
        }
        public String stat() {
            return "("+totcost+","+memcost+")";
        }
    }
    public static class MITMCalculator {
        int NP, K;
        int[][] PROFILES;
        Map<String,Integer> PROFILE2IDX;
        List<List<int[]>> PRODPAIRS;
        BigInteger[] COSTS;
        BigInteger mem_limit;
        public int profile2idx(int[] P) {
            return PROFILE2IDX.getOrDefault(Arrays.toString(P),-1);
        }
        public MITMCalculator(int[] H, int MAXR, int mem_limit) {
            K=H.length; this.mem_limit=new BigInteger(""+mem_limit);
            PROFILES=profiles(H,MAXR).toArray(new int[0][]); NP=PROFILES.length;
            PROFILE2IDX=new HashMap<>(); for (int pi=0; pi<NP; pi++) PROFILE2IDX.put(Arrays.toString(PROFILES[pi]),pi);

            COSTS=new BigInteger[NP];
            for (int pi=0; pi<NP; pi++) COSTS[pi]=profileCost(H,PROFILES[pi]);
            PRODPAIRS=new ArrayList<>(); for (int pi=0; pi<NP; pi++) PRODPAIRS.add(new ArrayList<>());
            for (int pa=0; pa<NP; pa++)
                if (COSTS[pa].compareTo(this.mem_limit)<=0)
                    for (int pb=0; pb<NP; pb++) {
                        int pi=profile2idx(eltsum(PROFILES[pa],PROFILES[pb]));
                        if (pi>=0) PRODPAIRS.get(pi).add(new int[] {pa,pb});
                    }
        }
        public MITM convert(Set<Integer> mS, Set<Integer> iS) {
            BigInteger totm=BigInteger.ZERO; for (int pi:mS) totm=totm.add(COSTS[pi]);
            BigInteger tot=totm; for (int pi:iS) tot=tot.add(COSTS[pi]);
            List<int[]> mPs=new ArrayList<>(), iPs=new ArrayList<>();
            for (int pi:mS) mPs.add(PROFILES[pi]);
            for (int pi:iS) iPs.add(PROFILES[pi]);
            return new MITM(mPs.toArray(new int[0][]),iPs.toArray(new int[0][]),totm,tot);
        }
        public MITM greedy(int[] ord) {
            Set<Integer> mS=new HashSet<>(), iS=new HashSet<>(); BigInteger totm=BigInteger.ZERO;
            for (int i:ord) {
                BigInteger bscr=null; int[] bpair=null;
                for (int[] pair:PRODPAIRS.get(i)) {
                    BigInteger dmem=mS.contains(pair[0])?BigInteger.ZERO:COSTS[pair[0]];
                    if ((totm.add(dmem)).compareTo(mem_limit)<=0) {
                        BigInteger scr=dmem.add(iS.contains(pair[1])?BigInteger.ZERO:COSTS[pair[1]]);
                        if (bscr==null || scr.compareTo(bscr)<0) {
                            bscr=scr;
                            bpair=pair;
                        }
                    }
                }
                if (bpair==null) return null;//throw new RuntimeException(i+" "+totm);
                if (!mS.contains(bpair[0])) totm=totm.add(COSTS[bpair[0]]);
                mS.add(bpair[0]);
                iS.add(bpair[1]);
            }
            return convert(mS,iS);
        }
        public MITM hill_climb(long REPS) {
            long st=System.currentTimeMillis();
            int[] ord=ArrayHelp.range(NP);
            MITM sol=greedy(ord);
            System.out.println("~~~ init_stat="+sol.stat());
            SplittableRandom rnd=new SplittableRandom(1);
            for (long reps=0, accn=0, mark=0; reps<REPS;) {
                int i=rnd.nextInt(NP), j=rnd.nextInt(NP-1);
                if (j>=i) j++;
                int oi=ord[i], oj=ord[j];
                ord[i]=oj; ord[j]=oi;
                MITM nsol=greedy(ord);
                if (nsol!=null && nsol.totcost.compareTo(sol.totcost)<=0) {
                    sol=nsol;
                    accn++;
                }
                else {
                    ord[i]=oi; ord[j]=oj;
                }
                reps++;
                long t=System.currentTimeMillis()-st;
                if (reps==REPS || t>=mark) {
                    System.out.printf("\tt=%d reps=%d scr=%d accn=%d%n",t,reps,sol.totcost,accn);
                    mark+=5000;
                }
            }
            System.out.println("~~~ fin_stat="+sol.stat());
            //System.out.println(ArrayHelp.inta2str(ord));
            return sol;
        }
        public void checkMITM(MITM mitm) {
            boolean[] seen=new boolean[NP];
            for (int[] pa:mitm.memPs) for (int[] pb:mitm.iterPs) {
                int pi=profile2idx(eltsum(pa,pb));
                if (pi>=0) seen[pi]=true;
            }
            for (boolean b:seen) if (!b) throw new RuntimeException();
        }
    }
}
abstract class CardDFS {
    private OrbitCollection O$;
    protected int D; private int[] groupIdxs;
    private int[] ois;
    private long work;
    abstract void process(int[] stem, int oi);
    abstract void process_stem(int[] stem);
    public int[] stem_card() { if (D==0) return new int[] {}; return Arrays.copyOf(ois,D-1); }
    public int[] card() { return Arrays.copyOf(ois,D); }
    private void dfs(int d, int lo, int[] vec) {
        if (d==D-1) process_stem(vec);
        int g=groupIdxs[d]; int[] oiList=O$.CANONICAL_ORBITS_BY_SIZE[g];
        for (int i=lo; i<oiList.length; i++) {
            int oi=oiList[i]; ois[d]=oi;
            if (d==D-1) {
                process(vec,oi); work++;
            }
            else dfs(d+1, d<D-1&&groupIdxs[d]==groupIdxs[d+1]?(i+1):0, O$.xorvec(vec,oi));
        }
    }
    public CardDFS(OrbitCollection O$, int[] profile, int[] init_vec) {
        if (O$.CANONICAL_ORBITS_BY_SIZE.length!=profile.length) throw new RuntimeException();
        this.O$=O$;
        D=0; for (int m:profile) if (m>=0) D+=m; else throw new RuntimeException();
        ois=new int[D];
        if (D==0) process(init_vec,OrbitCollection.NOT_ORBITIDX);
        else {
            groupIdxs=new int[D];
            for (int i=0, idx=0; i<O$.CANONICAL_ORBITS_BY_SIZE.length; i++)
                for (int rep=0; rep<profile[i]; rep++) groupIdxs[idx++]=i;
            work=0;
            dfs(0,0,init_vec);
            long expected_work=ProfileManagement.profileCost(O$.CANONICAL_ORANKHIST,profile).longValue();
            if (work!=expected_work) throw new RuntimeException(work+"!="+expected_work);
        }
    }
    public CardDFS(OrbitCollection O$, int[] mults) {
        this(O$,mults,new int[O$.WORDLEN]);
    }
}

abstract class CardParser {
    public static final long NOT_A_PAIR=-1, EMPTY_PAIR=-2;
    public final int W;
    CardParser(int W) { this.W=W; }
    public abstract int _word(long p, int w);
    public int word(long p, int w) {
        if (p==NOT_A_PAIR) throw new RuntimeException("Not a pair");
        if (p==EMPTY_PAIR) return 0;
        if (w<0 || w>=W) throw new RuntimeException(w+" not in [0,"+W+")");
        return _word(p,w);
    }
    public int compareBitset(long a, int[] vec) {
        for (int w=W-1; w>=0; w--) {
            int d=Integer.compareUnsigned(word(a,w),vec[w]);
            if (d!=0) return d;
        }
        return 0;
    }
    public int[] vec(long a) {
        int[] v=new int[W];
        for (int w=0; w<W; w++) v[w]=word(a,w);
        return v;
    }
    public abstract int[] _card(long p);
    public int[] card(long p) { if (p==NOT_A_PAIR) throw new RuntimeException(); if (p==EMPTY_PAIR) return new int[] {}; return _card(p); }
    public abstract int _rank(long p);
    public int rank(long p) { if (p==NOT_A_PAIR) throw new RuntimeException(); if (p==EMPTY_PAIR) return 0; return _rank(p); }
}
class Bitset {
    private static final int CHUNK_POW=6, CHUNK=1<<CHUNK_POW, CHUNKMODMASK=(1<<CHUNK_POW)-1;
    long[] A;
    public Bitset(long N) {
        if (N/CHUNK+1>=Integer.MAX_VALUE) throw new RuntimeException();
        A=new long[(int)(N/CHUNK+1)];
    }
    public void add(int v) {
        A[v>>>CHUNK_POW]|=1L<<(v&CHUNKMODMASK);
    }
    public boolean contains(int v) { return (A[v>>>CHUNK_POW]&(1L<<(v&CHUNKMODMASK)))!=0; }
}
class Filterer {
    public final int F, W;
    Bitset[] filters;
    public Filterer(int F) {
        this.F=F;
        W=(F-1)/32+1;
        filters=new Bitset[W];
        for (int f=0; f<F; f+=32) filters[f/32]=new Bitset(1L<<(Math.min(f+32,F)-f));
    }
    public void add(int[] vec) {
        for (int w=0; w<W; w++) filters[w].add(vec[w]);
    }
    public int first_fail(int[] vec) {
        for (int w=0; w<W; w++) if (!filters[w].contains(vec[w])) return w;
        return W;
    }
}
class Deck {
    private static void swap(long[] A, int i, int j) {
        long t=A[i]; A[i]=A[j]; A[j]=t;
    }
    //sort vals in ps based on their bit-vectors f.vec(p)
    //bit-vectors are ordered by ascending [W-1] index, unsigned int64 comparison,
    //  tie-break at [W-2] index, then at [W-3] index, ...
    //if equal bit-vectors: keep p with minimal f.rank(p), tiebreak on smallest integer p
    public static void sort_help(long[] A, CardParser f, int left, int right, int w, SplittableRandom rnd) {
        if (left>=right) return;
        if (w<0) { //only care about getting the min elem in this range
            long bp=CardParser.NOT_A_PAIR; int brank=Integer.MAX_VALUE;
            for (int i=left; i<=right; i++) {
                long p=A[i]; int r=f.rank(p);
                if (bp==CardParser.NOT_A_PAIR || r<brank || (r==brank && p<bp)) {
                    bp=p;
                    brank=r;
                }
            }
            A[left]=bp;
            for (int i=left+1; i<=right; i++) A[i]=CardParser.NOT_A_PAIR;
            return;
        }
        int pw=f.word(A[rnd.nextInt(left,right+1)],w);
        int low_end=left, pivot_end=left; //[left,low_end) are <pw, [low_end,pivot_end) are ==pw, rest are yet to be partitioned
        for (int i=left; i<=right; i++) {
            int d=Long.compareUnsigned(f.word(A[i],w),pw);
            if (d<0) {
                swap(A,low_end,i);
                if (pivot_end>low_end) swap(A,pivot_end,i);
                low_end++; pivot_end++;
            }
            else if (d==0) {
                swap(A,pivot_end,i); pivot_end++;
            }
        }
        if (low_end>=pivot_end) throw new RuntimeException();
        sort_help(A,f,left,low_end-1,w,rnd);
        sort_help(A,f,low_end,pivot_end-1,w-1,rnd); //the range [low_end,pivot_end) must have size at least 1
        sort_help(A,f,pivot_end,right,w,rnd);
    }
    public static long[] sortAndFilter(long[] A, CardParser f) { //NOTE: Will modify A
        sort_help(A,f,0,A.length-1,f.W-1,new SplittableRandom(1));
        int K=0;
        for (int i=0; i<A.length; i++)
            if (A[i]!=CardParser.NOT_A_PAIR) A[K++]=A[i];
        return Arrays.copyOf(A,K);
    }

    CardParser code_parser;
    long[] ps;
    Filterer filt=null; long[] nfailedat=null; long ntough;
    public Deck(int F, long[] pairs, CardParser code_parser, boolean have_filt) { //WARNING: mutates long[] pairs
        for (long p:pairs) if (p==CardParser.NOT_A_PAIR) throw new RuntimeException();
        this.code_parser=code_parser;
        ps=sortAndFilter(pairs,code_parser);
        if (have_filt) init_filter(F);
    }
    public void check(OrbitCollection O$) {
        long st=System.currentTimeMillis();
        for (long p:ps) { //ensure all cards, xor-vectors, and ranks are correct
            int[] card=code_parser.card(p);
            if (!Arrays.equals(O$.vec(card),code_parser.vec(p))) throw new RuntimeException();
            if (O$.rank(card)!=code_parser.rank(p)) throw new RuntimeException();
        }
        for (int i=1; i<ps.length; i++) //ensure all bit vector keys in our map data structure are distinct and in ascending order
            if (code_parser.compareBitset(ps[i-1],code_parser.vec(ps[i]))>=0) throw new RuntimeException();
        System.out.println("check_time="+(System.currentTimeMillis()-st));
    }
    private void init_filter(int F) {
        long filter_st=System.currentTimeMillis();
        filt=new Filterer(F);
        for (long p:ps) filt.add(code_parser.vec(p));
        for (long p:ps) if (filt.first_fail(code_parser.vec(p))!=filt.W) throw new RuntimeException();
        nfailedat=new long[filt.W]; ntough=0;
        System.out.println("filter_time="+(System.currentTimeMillis()-filter_st));
    }
    private long bin_search(int[] vec) {
        int lo=0, hi=ps.length-1;
        while (lo<hi) {
            int mi=(lo+hi)>>>1; //behaves correctly even when lo+hi overflows
            if (code_parser.compareBitset(ps[mi],vec)>=0) hi=mi;
            else lo=mi+1;
        }
        long p=ps[lo];
        return code_parser.compareBitset(p,vec)==0?p:CardParser.NOT_A_PAIR;
    }
    public long get(int[] stem, OrbitCollection O$, int oi) { //search for bit vector O$.xorvec(stem,oi)
        if (filt!=null) {
            for (int w=0; w<O$.WORDLEN; w++) {
                if (!filt.filters[w].contains(O$.xorword(stem,oi,w))) {
                    nfailedat[w]++;
                    return CardParser.NOT_A_PAIR;
                }
            }
            ntough++;
        }
        return bin_search(O$.xorvec(stem,oi));
    }
}
