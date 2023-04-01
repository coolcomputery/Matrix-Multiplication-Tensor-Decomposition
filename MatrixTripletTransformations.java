import java.util.*;
public class MatrixTripletTransformations {
    private static int bit(int n, int b) {
        return (n>>>b)&1;
    }
    private static int mod(int n, int k) {
        return ((n%k)+k)%k;
    }
    private static int gcd(int a, int b) {
        if (a>b) return gcd(b,a);
        if (a==0) return b;
        return gcd(a,b%a);
    }
    public static int[] list2arr(List<Integer> L) {
        int[] A=new int[L.size()]; for (int i=0; i<A.length; i++) A[i]=L.get(i);
        return A;
    }
    private static int[][] binprod(int[][] A, int[][] B) {
        if (A[0].length!=B.length) throw new RuntimeException();
        int[][] C=new int[A.length][B[0].length];
        for (int i=0; i<A.length; i++) for (int j=0; j<A[0].length; j++) for (int k=0; k<B[0].length; k++)
            C[i][k]^=A[i][j]&B[j][k];
        return C;
    }
    private static int[] arrAdd1(int[] A, int v) {
        int[] out=Arrays.copyOf(A,A.length+1);
        out[A.length]=v;
        return out;
    }

    private int N, N2, NMATS, MATMASK, NGLs;
    private int cI;
    private int[][] PROD; private int[] TRANSPOSED, INV, GLs, MAT2GLIDX;
    private int ID_FUNCCODE, NFUNCs;
    private int[] TPFUNCCODE, CYCFUNCCODE, INVFUNCCODE;
    public int matcode(int[][] M) {
        int out=0;
        for (int i=0; i<N2; i++) out|=M[i/N][i%N]<<i;
        return out;
    }
    public int[][] codemat(int v) {
        int[][] out=new int[N][N];
        for (int i=0; i<N2; i++) out[i/N][i%N]=bit(v,i);
        return out;
    }
    public int str2matcode(String s) {
        if (s.length()!=N2) throw new RuntimeException();
        int out=0;
        for (int i=0; i<N2; i++) {
            int b=s.charAt(i)-'0'; if (b<0 || b>1) throw new RuntimeException();
            out|=b<<i;
        }
        return out;
    }
    public String matcode2str(int mc) {
        StringBuilder s=new StringBuilder();
        for (int b=0; b<N2; b++) s.append(bit(mc,b));
        return s.toString();
    }
    public MatrixTripletTransformations(int N) {
        this.N=N;
        N2=N*N; NMATS=1<<N2; MATMASK=(1<<N2)-1;
        PROD=new int[NMATS][NMATS]; TRANSPOSED=new int[NMATS]; INV=new int[NMATS];
        int[][][] mats=new int[NMATS][][];
        cI=0; for (int r=0; r<N; r++) cI|=1<<(r*N+r);
        for (int c=0; c<NMATS; c++) {
            mats[c]=codemat(c);
            int[][] tm=new int[N][N];
            for (int i=0; i<N; i++) for (int j=0; j<N; j++) tm[i][j]=mats[c][j][i];
            TRANSPOSED[c]=matcode(tm);
        }
        Arrays.fill(INV,-1);
        for (int ca=0; ca<NMATS; ca++) for (int cb=0; cb<NMATS; cb++) {
            PROD[ca][cb]=matcode(binprod(mats[ca],mats[cb]));
            if (PROD[ca][cb]==cI) INV[ca]=cb;
        }
        { //invertible matrices (general linear transformations)
            List<Integer> invertibles=new ArrayList<>();
            for (int i=0; i<NMATS; i++) {
                int cm=i^cI;
                if (INV[cm]>=0) invertibles.add(cm);
            }
            GLs=list2arr(invertibles); NGLs=GLs.length;
            MAT2GLIDX=new int[NMATS]; Arrays.fill(MAT2GLIDX,-1);
            for (int i=0; i<NGLs; i++) MAT2GLIDX[GLs[i]]=i;
        }
        ID_FUNCCODE=params2code(cI,cI,cI,0,0);
        NFUNCs=NGLs*NGLs*NGLs*6;
        TPFUNCCODE=new int[NFUNCs]; CYCFUNCCODE=new int[NFUNCs]; INVFUNCCODE=new int[NFUNCs];
        for (int cf=0; cf<NFUNCs; cf++) {
            int[] f=code2func(cf);
            TPFUNCCODE[cf]=func2code(tpfunc(1,f));
            CYCFUNCCODE[cf]=func2code(cycfunc(1,f));
            INVFUNCCODE[cf]=func2code(invfunc(f));
        }
        /*for (int X:GLs) for (int Y:GLs) for (int Z:GLs) for (int c=0; c<3; c++) for (int t=0; t<2; t++) {
            int f=params2code(X,Y,Z,c,t);
            if (X!=trA(f) || Y!=trB(f) || Z!=trC(f) || c!=cyc_pow(f) || t!=tp_pow(f)) throw new RuntimeException();
        }
        { //check function<-->int conversion, cyc, tp, and inverse are correct
            System.out.println("test cyc*, tp*, inv, id*, *id");
            long st=System.currentTimeMillis(), mark=0, work=0;
            for (int f=0; f<NFUNCs; f++) {
                long time=System.currentTimeMillis()-st;
                if (time>=mark) {
                    mark+=10_000;
                    System.out.printf("time=%d work=%d%n",time,work);
                }
                int cycf=CYCFUNCCODE[f], tpf=TPFUNCCODE[f], invf=INVFUNCCODE[f];
                for (int i=0; i<3*N2; i++) {
                    int ctri=1<<i; //basis matrix triplet
                    int fctri=transformedctri(f,ctri);
                    if (transformedctri(cycf,ctri)!=cyc_ctri(fctri)) throw new RuntimeException();
                    if (transformedctri(tpf,ctri)!=tp_ctri(fctri)) throw new RuntimeException();
                    if (transformedctri(invf,fctri)!=ctri) throw new RuntimeException();
                }
                if (f!=comp(f,ID_FUNCCODE) || f!=comp(ID_FUNCCODE,f)) throw new RuntimeException();
                work++;
            }
            System.out.printf("time=%d work=%d%n",System.currentTimeMillis()-st,work);
        }*/
    }

    //            notation:
//            @ denotes matrix multiplication
//            * between two functions denotes function composition
//            for a matrix M, iM denotes the inverse of M; M.T denotes the transpose of M
//
//            functions:
//            where A,B,C,X,Y,Z are NxN matrices:
//            cyc((A,B,C))=(B,C,A)
//            tp((A,B,C))=(C.T,B.T,A.T)
//            tr((X,Y,Z))((A,B,C))=(X@A@iY,Y@B@iZ,Z@C@iX)
//
//
//            properties:
//            cyc^3=tp^2=tr((I,I,I))=identity
//            (* represents function composition)
//            tp*cyc=(cyc^2)*tp
//            cyc*tr((X,Y,Z))=tr((Y,Z,X))*cyc
//            tp*tr((X,Y,Z))=tr((iX.T,iZ.T,iY.T))
//            all functions generated by <cyc,tp,tr((X,Y,Z))> can be written in the form
//                tr((X,Y,Z))*(cyc^c)*(tp^t) for NxN X,Y,Z, integer 0<=c<3 and 0<=t<2
//                --> represent as (X,Y,Z,c,t); encode to integer (tricode(X,Y,Z)*3+c)*2+t
    private int[] cycfunc(int c, int[] f0) { //(cyc^c)*f0
        c=mod(c,3);
        int[] f=Arrays.copyOf(f0,f0.length);
        for (int rep=0; rep<c; rep++) { //cyc*( tr((X,Y,Z))*(cyc^c)*(tp^t) )=tr((Y,Z,X))*(cyc^(c+1))*(tp^t)
            int ma=f[0], mb=f[1], mc=f[2];
            f[0]=mb; f[1]=mc; f[2]=ma;
            f[3]=mod(f[3]+1,3);
        }
        return f;
    }
    private int[] tpfunc(int t, int[] f0) { //(tp^t)*f0
        t=mod(t,2);
        int[] f=Arrays.copyOf(f0,f0.length);
        for (int rep=0; rep<t; rep++) { //tp*( tr((X,Y,Z))*(cyc^c)*(tp^t) )=tr((iX.T,iZ.T,iY.T))*(cyc^(2*c))*(tp^(t+1))
            int ma=f[0], mb=f[1], mc=f[2];
            f[0]=TRANSPOSED[INV[ma]]; f[1]=TRANSPOSED[INV[mc]]; f[2]=TRANSPOSED[INV[mb]];
            f[3]=mod(2*f[3],3); f[4]=mod(f[4]+1,2);
        }
        return f;
    }
    /*private int[] trfunc(int X, int Y, int Z, int[] f) { //tr(trtri)*f
        //tr((A,B,C))*( tr((X,Y,Z))*(cyc^c)*(tp^t) )=tr((AX,BY,CZ))*(cyc^c)*(tp^t)
        return new int[] {PROD[X][f[0]],PROD[Y][f[1]],PROD[Z][f[2]],f[3],f[4]};
    }
    private int[] comp(int[] f0, int[] f1) { //f0*f1
        return trfunc(f0[0],f0[1],f0[2], cycfunc(f0[3], tpfunc(f0[4], f1)));
    }*/
    private int[] invfunc(int[] f) {
        return tpfunc(-f[4],cycfunc(-f[3],new int[] {INV[f[0]],INV[f[1]],INV[f[2]],0,0}));
    }

    private int code2triA(int ctri) { return ctri&MATMASK; }
    private int code2triB(int ctri) { return (ctri>>>N2)&MATMASK; }
    private int code2triC(int ctri) { return (ctri>>>(2*N2))&MATMASK; }
    private int tri2code(int a, int b, int c) {
        return a|(b<<N2)|(c<<(2*N2));
    }
    private int cyc_ctri(int ctri) {
        return tri2code(code2triB(ctri),code2triC(ctri),code2triA(ctri));
    }
    private int tp_ctri(int ctri) {
        return tri2code(TRANSPOSED[code2triC(ctri)],TRANSPOSED[code2triB(ctri)],TRANSPOSED[code2triA(ctri)]);
    }
    private int tr_ctri(int cX, int cY, int cZ, int ctri) {
        return tri2code(
                PROD[PROD[cX][code2triA(ctri)]][INV[cY]],
                PROD[PROD[cY][code2triB(ctri)]][INV[cZ]],
                PROD[PROD[cZ][code2triC(ctri)]][INV[cX]]
        );
    }
    private int transformedctri(int f, int ctri) {
        for (int rep=tp_pow(f); rep>0; rep--) ctri=tp_ctri(ctri);
        for (int rep=cyc_pow(f); rep>0; rep--) ctri=cyc_ctri(ctri);
        return tr_ctri(trA(f),trB(f),trC(f),ctri);
    }

    private int func2code(int[] f) {
        //xor each encoded matrix with cI, so that the identity matrix will have index 0
        int ai=MAT2GLIDX[f[0]], bi=MAT2GLIDX[f[1]], ci=MAT2GLIDX[f[2]];
        if (ai<0 || bi<0 || ci<0) throw new RuntimeException();
        return ((ai+bi*NGLs+ci*NGLs*NGLs)*3+mod(f[3],3))*2+mod(f[4],2);
    }
    private int params2code(int X, int Y, int Z, int c, int t) {
        int ai=MAT2GLIDX[X], bi=MAT2GLIDX[Y], ci=MAT2GLIDX[Z]; if (ai<0 || bi<0 || ci<0) throw new RuntimeException();
        if (c<0 || c>=3) throw new RuntimeException();
        if (t<0 || t>=2) throw new RuntimeException();
        return ((ai+bi*NGLs+ci*NGLs*NGLs)*3+c)*2+t;
    }
    private int[] code2func(int cf) {
        ensure(cf);
        int ctr=(cf/2)/3;
        //xor is self-inverting
        return new int[] {GLs[ctr%NGLs],GLs[(ctr/NGLs)%NGLs],GLs[(ctr/NGLs)/NGLs],(cf/2)%3,cf%2};
    }
    private void ensure(int cf) { if (cf<0 || cf>=NFUNCs) throw new RuntimeException(); }
    private int tp_pow(int cf) { ensure(cf); return cf%2; }
    private int cyc_pow(int cf) { ensure(cf); return (cf/2)%3; }
    private int trA(int cf) { ensure(cf); int ctr=(cf/2)/3; return GLs[ctr%NGLs]; }
    private int trB(int cf) { ensure(cf); int ctr=(cf/2)/3; return GLs[(ctr/NGLs)%NGLs]; }
    private int trC(int cf) { ensure(cf); int ctr=(cf/2)/3; return GLs[(ctr/NGLs)/NGLs]; }
    private int trfunccode(int X, int Y, int Z, int cf) {
        return params2code(PROD[X][trA(cf)],PROD[Y][trB(cf)],PROD[Z][trC(cf)],cyc_pow(cf),tp_pow(cf));
    }
    private int comp(int cfa, int cfb) {
        int out=cfb;
        switch (tp_pow(cfa)) {
            case 0: break;
            case 1: out=TPFUNCCODE[out]; break;
            default: throw new RuntimeException();
        }
        switch (cyc_pow(cfa)) {
            case 0: break;
            case 1: out=CYCFUNCCODE[out]; break;
            case 2: out=CYCFUNCCODE[CYCFUNCCODE[out]]; break;
            default: throw new RuntimeException();
        }
        return trfunccode(trA(cfa),trB(cfa),trC(cfa),out);
        //return params2code(PROD[trA(cfa)][trA(out)],PROD[trB(cfa)][trB(out)],PROD[trC(cfa)][trC(out)],cyc_pow(out),tp_pow(out));
    }
    private int conj(int f, int g) { //return fgf^{-1}
        return comp(comp(f,g),INVFUNCCODE[f]);
    }

    public String funccode2str(int cf) {
        StringBuilder s=new StringBuilder("tr"+matcode2str(trA(cf))+"-"+matcode2str(trB(cf))+"-"+matcode2str(trC(cf)));
        for (int rep=cyc_pow(cf); rep>0; rep--) s.append("@cyc");
        for (int rep=tp_pow(cf); rep>0; rep--) s.append("@tp");
        return s.toString();
    }
    public int str2funccode(String s) {
        String[] pcs=s.split("@");
        int cf=ID_FUNCCODE;
        for (int i=pcs.length-1; i>=0; i--) {
            String pc=pcs[i];
            if (pc.equals("cyc")) cf=CYCFUNCCODE[cf];
            else if (pc.equals("tp")) cf=TPFUNCCODE[cf];
            else if (!pc.equals("")) {
                if (!pc.startsWith("tr")) throw new RuntimeException();
                String[] matstrs=pc.substring(2).split("-");
                if (matstrs.length!=3) throw new RuntimeException();
                cf=trfunccode(str2matcode(matstrs[0]),str2matcode(matstrs[1]),str2matcode(matstrs[2]),cf);
            }
        }
        return cf;
    }
    public int[] str2funccodes(String s) {
        List<Integer> out=new ArrayList<>();
        for (String fstr:s.split(",")) if (!fstr.equals(""))
            out.add(str2funccode(fstr));
        return list2arr(out);
    }
    public String funccodes2str(int[] S) {
        StringBuilder s=new StringBuilder(); for (int e:S) s.append(s.length()>0?",":"").append(funccode2str(e));
        return s.toString();
    }

    class Subgroup {
        private int[] gset;
        private Set<Integer> elems;
        private Queue<Integer> todo;
        private boolean entire_group;
        public long work;
        public Subgroup(int[] gset, boolean construct_all) {
            this.gset=gset;
            elems=new HashSet<>(Collections.singletonList(ID_FUNCCODE));
            todo=new ArrayDeque<>(Collections.singletonList(ID_FUNCCODE));
            entire_group=false;
            work=0;
            if (construct_all) construct_all();
        }
        public Subgroup(int[] gset) {
            this(gset,false);
        }
        private boolean complete() {
            return todo.size()==0;
        }
        private void bfs_step() {
            if (complete()) throw new RuntimeException();
            int g=todo.remove();
            for (int s:gset) {
                int h=comp(s,g);
                if (!elems.contains(h)) {
                    elems.add(h);
                    todo.add(h);
                }
                work++;
            }
            if (2*elems.size()>NFUNCs) { //Lagrange's thm.: after completion, elems.size() must be a divisor of NFUNCs
                entire_group=true;
                elems=null;
                todo.clear();
            }
        }
        public void construct_all() {
            while (!complete()) bfs_step();
        }
        public int size() {
            if (!complete()) throw new RuntimeException();
            return entire_group?NFUNCs:elems.size();
        }
        public boolean contains(int e) {
            while (true) {
                if (entire_group || elems.contains(e)) return true;
                if (!complete()) bfs_step();
                else break;
            }
            return false;
        }
        public boolean containsConjugateOf(int f, int[] T) {
            for (int t:T) if (!contains(conj(f,t))) return false;
            return true;
        }
        //(group G contains fSf^{-1}) <==> (G contains f<S>f^{-1})
        public boolean equalsConjugateOfGroup(int f, Subgroup H) {
            return containsConjugateOf(f,H.gset) && H.containsConjugateOf(INVFUNCCODE[f],gset);
        }
        public boolean conjugatesToSelf(int f) {
            //(<S>=f<S>f^{-1}) <==> (<S> contains fSf^{-1}), since <S> and f<S>f^{-1} have equal size
            return containsConjugateOf(f,gset);
        }
    }
    public boolean haveConjugateGenerations(String Astr, String Bstr) {
        int[] A=str2funccodes(Astr), B=str2funccodes(Bstr);
        Subgroup G=new Subgroup(A,true), H=new Subgroup(B);
        System.out.printf("G=<%s>=%s%nH=<%s>%n",Astr,G.elems,Bstr);
        for (int f=0; f<NFUNCs; f++) {
            if (H.equalsConjugateOfGroup(f,G)) {
                H.construct_all();
                System.out.printf("H=fG(f^{-1})=%s f=%s f^{-1}=%s%n",H.elems,funccode2str(f),funccode2str(INVFUNCCODE[f]));
                return true;
            }
        }
        H.construct_all();
        System.out.println("H="+H.elems+" is not a conjugate of G");
        return false;
    }

    private int[] normalizer(Subgroup G) {
        List<Integer> normalizer=new ArrayList<>();
        for (int f=0; f<NFUNCs; f++)
            if (G.contains(f) || G.conjugatesToSelf(f)) normalizer.add(f);
        return list2arr(normalizer);
    }
    private List<Integer> leftCosetReps(int[] H) {
        boolean[] seen=new boolean[NFUNCs];
        List<Integer> out=new ArrayList<>();
        for (int f=0; f<NFUNCs; f++) if (!seen[f]) {
            out.add(f);
            for (int h:H) seen[comp(f,h)]=true;
        }
        return out;
    }
    private List<Integer> conjugate_totientPowers(int f, int[] conjers) {
        //return { (n*f*n^{-1})^k for all n in conjers, k coprime to ord(f) }
        //(n*f*n^{-1})^k = n*(f^k)*n^{-1}
        List<Integer> nonredundantConjugators; {
            nonredundantConjugators=new ArrayList<>();
            Set<Integer> seen=new HashSet<>();
            for (int n:conjers) {
                int g=conj(n,f);
                if (!seen.contains(g)) {
                    nonredundantConjugators.add(n);
                    seen.add(g);
                }
            }
        }
        List<Integer> fpows=new ArrayList<>();
        for (int fpow=ID_FUNCCODE, pow=0; fpow!=ID_FUNCCODE || pow==0; fpow=comp(f,fpow), pow++)
            fpows.add(fpow);
        int f_ord=fpows.size();
        List<Integer> out=new ArrayList<>();
        for (int i=0; i<f_ord; i++) if (gcd(i,f_ord)==1)
        for (int n:nonredundantConjugators)
            out.add(conj(n,fpows.get(i)));
        return out;
    }
    private List<String> generatingSetsAdd1_mod_conj(String Sstr) {
        System.out.println("enumerating <S,f> up to conjugacy; S=["+Sstr+"]");
        int[] S=str2funccodes(Sstr);
        Set<Integer> gS=new Subgroup(S,true).elems; System.out.println("|<S>|="+gS.size());
        int[] N_gS=normalizer(new Subgroup(S)); System.out.printf("|N(<S>)|=%d%n",N_gS.length);
        //<S,f> = < <S>,<f> >
        long st=System.currentTimeMillis(), mark=0, nprocessed=0, work=0, check_bfs_work=0, check_time=0, gen_time=0, elim_time=0;
        boolean[] processed=new boolean[NFUNCs];
        class Canon {
            Subgroup G;
            List<Integer> testConjugators; //left coset reps of N(G)
            public Canon(Subgroup G) {
                this.G=G;
                G.construct_all();
                testConjugators=leftCosetReps(normalizer(G));
            }
        }
        List<Canon> canons=new ArrayList<>();
        for (int f=0; f<NFUNCs; f++) if (!processed[f]) {
            int[] gset=arrAdd1(S,f);
            {
                long t=System.currentTimeMillis()-st;
                if (t>=mark) {
                    System.out.printf("time=%d nprocessed=%d work=%d #groups=%d f=%d check_time=%d avg(check_bfs_work)=%.2f gen_time=%d elim_time=%d%n",
                            t,nprocessed,work,canons.size(),f,check_time,check_bfs_work/(double)work,gen_time,elim_time);
                    while (t>=mark) mark+=mark<100_000?10_000:mark<1000_000?100_000:1000_000;
                }
            }
            check_time-=System.currentTimeMillis();
            Subgroup sbgp=new Subgroup(gset);
            boolean good=true;
            //<S>=g^{-1}<T>g for some g iff <S> contains g^{-1}Tg and <T> contains gSg^{-1}
            for (Canon C:canons) {
                for (int j:C.testConjugators)
                    if (C.G.equalsConjugateOfGroup(INVFUNCCODE[j],sbgp)) {
                        good=false;
                        break;
                    }
                if (!good) break;
            }
            check_bfs_work+=sbgp.work;
            check_time+=System.currentTimeMillis();
            if (good) {
                gen_time-=System.currentTimeMillis();
                Canon C=new Canon(sbgp);
                System.out.printf("\tf=%d |<S,f>|=%d%n",f,C.G.size());
                canons.add(C);
                gen_time+=System.currentTimeMillis();
            }
            elim_time-=System.currentTimeMillis();
            List<Integer> to_elim=new ArrayList<>(Collections.singletonList(f)), method=new ArrayList<>(Collections.singletonList(-1));
            Set<Integer> elim_set=new HashSet<>(Collections.singletonList(f)); {
                long elim_st=System.currentTimeMillis(), elim_mark=0, elim_work=0;
                for (int i=0; i<to_elim.size(); i++) {
                    long t=System.currentTimeMillis()-elim_st;
                    if (t>=elim_mark) {
                        if (elim_mark>0) System.out.printf("\t\tt=%d i=%d cnt=%d work=%d%n",t,i,elim_set.size(),elim_work);
                        elim_mark+=elim_mark<100_000?10_000:elim_mark<1000_000?100_000:1000_000;
                    }
                    int g=to_elim.get(i), m=method.get(i);
                    if (m!=0) {
                        for (int h:conjugate_totientPowers(g,N_gS)) {
                            elim_work++;
                            if (!elim_set.contains(h)) {
                                elim_set.add(h);
                                to_elim.add(h);
                                method.add(0);
                            }
                        }
                    }
                    if (m!=1) {
                        Set<Integer> neighbors=new HashSet<>();
                        for (int s:gS) neighbors.add(comp(s,g));
                        for (int h:neighbors) {
                            elim_work++;
                            if (!elim_set.contains(h)) {
                                elim_set.add(h);
                                to_elim.add(h);
                                method.add(1);
                            }
                        }
                    }
                    if (m!=2) {
                        Set<Integer> neighbors=new HashSet<>();
                        for (int s:gS) neighbors.add(comp(g,s));
                        for (int h:neighbors) {
                            elim_work++;
                            if (!elim_set.contains(h)) {
                                elim_set.add(h);
                                to_elim.add(h);
                                method.add(2);
                            }
                        }
                    }
                }
                System.out.printf("\telim: t=%d cnt=%d work=%d%n",System.currentTimeMillis()-elim_st,elim_set.size(),elim_work);
            }
            for (int g:to_elim) {
                if (!processed[g]) nprocessed++;
                processed[g]=true;
            }
            elim_time+=System.currentTimeMillis();
            work++;
        }
        System.out.printf("time=%d nprocessed=%d work=%d #groups=%d check_time=%d avg(check_bfs_work)=%.2f gen_time=%d elim_time=%d%n",
                System.currentTimeMillis()-st,nprocessed,work,canons.size(),check_time,check_bfs_work/(double)work,gen_time,elim_time);
        List<String> out=new ArrayList<>();
        for (Canon c:canons) out.add(funccodes2str(c.G.gset));
        return out;
    }
    public static void main(String[] args) {
        MatrixTripletTransformations $=new MatrixTripletTransformations(3);
        for (String s:new String[] {"tr101110001-100010001-100010001@cyc","cyc,tr101110001-101110001-101110001","cyc,tr010100001-100010001-100010001@tp"})
            System.out.println($.haveConjugateGenerations("cyc,tr001101011-001101011-001101011",s));
        for (String gset0:new String[] {"cyc"}) System.out.println($.generatingSetsAdd1_mod_conj(gset0));
        //System.out.println($.new Subgroup($.str2funccodes("cyc,tr101110001-100010001-100010001@tp"),true).size());
    }
}
