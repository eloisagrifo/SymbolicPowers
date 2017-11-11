newPackage(
        "SymbolicPowers",
	Version => "1.1", 
	Date => "November 8, 2017",
	Authors => {
	    {Name => "Eloisa Grifo", Email => "eloisa.grifo@virginia.edu", HomePage => "http://people.virginia.edu/~er2eq/"}
	    },
	Headline => "Calculations involving symbolic powers",
	DebuggingMode => false
        )


export {
    -- Options
    "InSymbolic",
    "SampleSize",
    "UseMinimalPrimes",
    "UseWaldschmidt", 
    
    -- Methods
    "asymptoticRegularity",
    "assPrimesHeight",
    "bigHeight",
    "containmentProblem", 
    "exponentsMonomialGens", 
    "frobeniusPower",       
    "joinIdeals",    
    "isKonig", 
    "isPacked", 
    "isSymbolicEqualOrdinary",
    "isSymbPowerContainedinPower", 
    "lowerBoundResurgence",
    "minDegreeSymbPower", 
    "noPackedSub", 
    "noPackedAllSubs",
    "squarefreeGens", 
    "squarefreeInCodim",    
    "symbolicContainmentMonomialCurve",
    "symbolicDefect",
    "symbolicPower", 
    "symbolicPowerJoin",
    "symbolicPowerMonomialCurve", 
    "symbPowerPrimePosChar",
    "symbolicPolyhedron", 
    "minimalPart",
    "waldschmidt"
    }


needsPackage "Polyhedra";
needsPackage "Depth";



---------------------------------------------------------------
---------------------------------------------------------------
-- Auxiliary functions: faster powers, big height, minimal part
-- isMonomial
---------------------------------------------------------------
---------------------------------------------------------------

fastPower = method(TypicalValue => Ideal)
fastPower(Ideal,ZZ) := Ideal => (I,n) ->
(J := I;
(for i from 2 to n do J = J*I);
J)


--old version of big height
--bigHeight = method(TypicalValue => ZZ)
--bigHeight(Ideal) := ZZ => I -> (if isPrimary(I) then codim(I) else 
--    (R := ring I; d := dim R; c := codim I; M := R^1/I; 
--	if codim Ext^d(M,R) == d then d else
--	(l := toList (c .. d);
--	w := apply(l, i->Ext^i(M,R)); v := apply(w,codim); 
--	d-position(reverse(v-l),i->i==0))))


bigHeight = method(TypicalValue => ZZ)
bigHeight(Ideal) := ZZ => I -> (if isPrimary(I) then codim(I) else 
    (R := ring I; 
	d := dim R; 
	c := codim I; 
	M := R^1/I; 
	ans := d;
	scan(reverse toList (c .. d), 
	    i -> (if codim Ext^i(M,R) == i then (ans = i; break)));
	ans    	    	
	)
    )


assPrimesHeight = method(TypicalValue => List)
assPrimesHeight(Ideal) := List => I -> (
    if isPrimary(I) then {codim(I)} else 
    (R := ring I; 
	d := dim R; 
	c := codim I; 
	M := R^1/I; 
	l := toList (c .. d);
	w := apply(l, i->Ext^i(M,R)); 
	v := apply(w,codim);
	reverse apply(positions(reverse(v-l),i->i==0), j -> d-j)))



minimalPart = method()
minimalPart(Ideal) := Ideal => I -> (minPrimes := minimalPrimes (I);
    primDec := primaryDecomposition(I);
    minComponents := {};
    scan(primDec, i -> (rad := radical(i); scan(minPrimes, a -> 
		if rad == a then 
		(minComponents = append(minComponents,i); break))));
    intersect(minComponents))


isMonomial = method()
isMonomial(RingElement) := r -> (terms(r) == {r})
isMonomial(MonomialIdeal) := I -> true
isMonomial(Ideal) := I -> all(flatten entries mingens I,a -> isMonomial(a))


minDegreeSymbPower = method(TypicalValue => ZZ)
minDegreeSymbPower(Ideal,ZZ) := ZZ => (I,n) -> min flatten degrees symbolicPower(I,n)

--Given an ideal I and q=p^e, computes the e-th Frobenius power of I
frobeniusPower = method(TypicalValue => Ideal)
frobeniusPower(Ideal,ZZ) := Ideal => (I,q) -> 
ideal(apply(flatten entries gens I, i -> i^q))






-----------------------------------------------------------
-----------------------------------------------------------
-- Main symbolic powers function
-----------------------------------------------------------
-----------------------------------------------------------



symbPowerMon = method(TypicalValue => Ideal)
symbPowerMon(Ideal,ZZ) := Ideal => (I,n) -> (
    if not(isMonomialIdeal(I)) then "Not a monomial ideal!" else (
	--If I is square-free, the symbolic powers of I are obtained by 
	--intersecting the powers of its associated primes
    if isSquareFree I then 
    (assP := associatedPrimes(I); 
    intersect apply(assP, i -> fastPower(i,n)))
    else (
    --If I is simply monomial, one can collect the primary components in a decomposition
    --of I and intersect the powers of the *maximal* ones
    Pd:=primaryDecomposition I;
    P:=apply(Pd, a-> radical a);
    maxP:={};
    apply(P, a-> if #select(P, b-> isSubset(a,b))==1 then maxP=maxP|{a});
    Q:=for p in maxP list (intersect select(Pd, a-> isSubset(a,p)));
    intersect apply(Q,i -> fastPower(i,n)))))

symbPowerPrime = method()
symbPowerPrime(Ideal,ZZ) := Ideal => (I,n) -> (if not(isPrime(I)) 
    then "Not a prime ideal" else (primaryList := primaryDecomposition(fastPower(I,n)); 
	local result;
	scan(primaryList, i -> if radical(i)==I then (result = i; break));
	result))
    
symbPowerPrimary = method()
symbPowerPrimary(Ideal, ZZ) := Ideal => (I,n) -> (if not(isPrimary(I)) 
    then "Not a primary ideal" else (rad := radical(I);
	local result;
	primaryList := primaryDecomposition(fastPower(I,n)); 
	scan(primaryList,i->(if radical(i)==rad then result := i; break));
	result))
    
symbPowerSat = method(TypicalValue => Ideal)
symbPowerSat(Ideal,ZZ) := Ideal => (I,n) -> (R := ring I; 
    m := ideal vars R; 
    saturate(fastPower(I,n),m))

--Takes a primary decomposition of I^n, picks the components corresponding to the 
--minimal primes of I and intersects them
symbPowerSlow = method(TypicalValue => Ideal)
symbPowerSlow(Ideal,ZZ) := Ideal => (I,n) -> (assI := associatedPrimes(I);
    decomp := primaryDecomposition fastPower(I,n);
    intersect select(decomp, a -> any(assI, i -> radical a==i)))


symbolicPower = method(TypicalValue => Ideal, Options => {UseMinimalPrimes => false})
symbolicPower(Ideal,ZZ) := Ideal => opts -> (I,n) -> (R := ring I;

    if opts.UseMinimalPrimes then return (minimalPart fastPower(I,n));
        
    if not opts.UseMinimalPrimes then (    
    	if (codim I == dim R - 1 and isHomogeneous(I)) then (
	    if depth (R/I) == 0 then return fastPower(I,n) else 
		return symbPowerSat(I,n) 
	    ) else (
	    if (isPolynomialRing R and isMonomial I) then (
		return symbPowerMon(monomialIdeal(I),n)
		) else (
		    if isPrime I then return symbPowerPrime(I,n) else 
	    	    if isPrimary I then return symbPowerPrimary(I,n) else 
			return symbPowerSlow(I,n)
	    	    )
		)	    
    )       
    )



-----------------------------------------------------------
-----------------------------------------------------------
-- Containment Problem and Equality functions
-----------------------------------------------------------
-----------------------------------------------------------


isSymbolicEqualOrdinary = method(TypicalValue => Boolean)
isSymbolicEqualOrdinary(Ideal,ZZ) := (P,n) -> (Q := fastPower(P,n); 
    h := bigHeight(P);
    if bigHeight(Q) > h then false else (
	if h==codim(P) then true else symbolicPower(P,n)==Q))
    



isSymbPowerContainedinPower = method(TypicalValue => Boolean, Options => {UseMinimalPrimes => false})
isSymbPowerContainedinPower(Ideal,ZZ,ZZ) := Boolean => opts -> (I,m,n) -> (
    h := bigHeight I; 
    if m<n then false else (
	if m>= h*n then true else (
	symb := symbolicPower(I,m, UseMinimalPrimes => opts.UseMinimalPrimes); 
	pow := fastPower(I,n); 
	isSubset(symb,pow))))




containmentProblem = method(TypicalValue => ZZ, Options => {UseMinimalPrimes => false,InSymbolic => false})
containmentProblem(Ideal,ZZ) := ZZ => opts -> (I,n) -> (

    if not(opts.InSymbolic) then (
	m := n; 
	while 
	not(isSymbPowerContainedinPower(I,m,n, UseMinimalPrimes => opts.UseMinimalPrimes)) 
	do m = m+1; return(m));
    
    if opts.InSymbolic then (
    h := bigHeight(I);
    e := (n-n%h)/h; 
    l := lift(e,ZZ);
    while isSymbPowerContainedinPower(I,n,l+1,
	UseMinimalPrimes => opts.UseMinimalPrimes) do l = l+1;
    return l))





-----------------------------------------------------------
-----------------------------------------------------------
--Other ways to compute symbolic powers: 
--for primes in char p
--for prime ideals in a polynomial ring, using join
-----------------------------------------------------------
-----------------------------------------------------------



--Given integers a and p, finds the largest power of p such that p^k<=a
--auxiliary for symbPowerPrimePosChar
powersdivision = method(TypicalValue => ZZ)
powersdivision(ZZ,ZZ,ZZ) := ZZ => (a,p,k) -> (if p^k>a then 1 else 
    1+(powersdivision(a,p,k+1)))
powersdivision(ZZ,ZZ) := ZZ => (a,p) -> powersdivision(a,p,1)


--Computes the symbolic power of a prime ideal in characteristic p
--The method is as follows: to compute $I^{(a)}$, find the largest value k with 
-- $q=p^k \leqslant a$
--$I^{(a)} = (I^{[q]} : I^{a-q+1})$
symbPowerPrimePosChar = method(TypicalValue => Ideal)
symbPowerPrimePosChar(Ideal,ZZ) := Ideal => (I,n) -> (R := ring I; p := char R;
    if not(isPrime(I)) 
    then "Not a prime ideal" else (
	h := codim I;
	if p==0 then "The characteristic must be positive" else
	(e := powersdivision(n,p); q := p^e; c := q-1; d := h*c-n+1; J:= I^d;
	    (frobeniusPower(I,q)):J)))


joinIdeals = method(TypicalValue => Ideal)
joinIdeals(Ideal,Ideal) := Ideal => (I,J) -> (R := ring I; k := coefficientRing(R);
    d := dim(R);
    S := k[vars 1 .. vars (3*d)];
    i := map(S, R, {(vars (d+1))_S .. (vars (2*d))_S});
    j := map(S, R, {(vars (2*d+1))_S .. (vars (3*d))_S});
    use S;
    aux := i -> (vars i)_S - (vars (d+i))_S - (vars (2*d+i))_S;
    extra := apply(toList(1 .. d), aux);
    bigideal := ideal(i(I),j(J), ideal(extra));
    inc := map(S,R,{(vars 1)_S .. (vars d)_S});
    preimage(inc,bigideal)
    );
    
    
symbolicPowerJoin = method(TypicalValue => Ideal);
symbolicPowerJoin(Ideal,ZZ) := Ideal => (p,n) -> (m := ideal(generators ring p);
    joinIdeals(p,m^n))



-----------------------------------------------------------
-----------------------------------------------------------
--Space monomial curves
-----------------------------------------------------------
-----------------------------------------------------------
    
curveIdeal = method(TypicalValue => Ideal)
curveIdeal(List) := Ideal => L -> (d := #L; 
    R := QQ(monoid[vars 1 .. vars d]); S := QQ(monoid[vars 0]); t := (gens S)_0;
    f := map(S,R,apply(L,i->t^i)); ker f)
curveIdeal(Ring,List) := Ideal => (k,L) -> (d := #L; 
    R := k(monoid[vars 1 .. vars d]); S := k(monoid[vars 0]); t := (gens S)_0;
    f := map(S,R,apply(L,i->t^i)); ker f)
    
symbolicContainmentMonomialCurve = method(TypicalValue => Boolean);
symbolicContainmentMonomialCurve(List,ZZ,ZZ) := Boolean => (L,m,n) -> (
    I := curveIdeal(L);
    isSymbPowerContainedinPower(I,m,n))
symbolicContainmentMonomialCurve(Ring,List,ZZ,ZZ) := Boolean => (k,L,m,n) -> (
    I := curveIdeal(k,L);
    isSymbPowerContainedinPower(I,m,n))

symbolicPowerMonomialCurve = method(TypicalValue => Ideal);
symbolicPowerMonomialCurve(List,ZZ) := Ideal => (L,m) -> (
    I := curveIdeal(L); symbolicPower(I,m))
symbolicPowerMonomialCurve(Ring,List,ZZ) := Ideal => (k,L,m) -> (
    I := curveIdeal(k,L); symbolicPower(I,m))

-----------------------------------------------------------
-----------------------------------------------------------
--Packing Problem
-----------------------------------------------------------
-----------------------------------------------------------

--Given a monomial ideal, finds a minimal generating set, 
--and then returns the exponents of the monomials in that set
--Given a monomial, returns the exponents

exponentsMonomialGens = method(TypicalValue => List)
exponentsMonomialGens(Ideal) := List => I -> (
    local L; 
    L = flatten entries mingens I;
    apply(L, l -> flatten exponents l)    
    )

squarefreeGens = method()
squarefreeGens(Ideal) := List => I ->(
    w := exponentsMonomialGens(I);
    v := select(w,i -> all(i,o -> o<2));
    R := ring I;
    l := flatten entries vars R;
    apply(v,o->product(apply(toList pairs(o),(i,j)->(l_i)^j))))


--Finds squarefree monomials generating I^c, where c=codim I
squarefreeInCodim = method()
squarefreeInCodim(Ideal) := List => I -> (c := codim I;
    J := fastPower(I,c);
    squarefreeGens(J))


isKonig = method(TypicalValue => Boolean)
isKonig(Ideal) := Boolean => I -> (
    R := ring I;
    if I == ideal 1_R then true else (
	if I == ideal(0_R) then true else (
	    c := codim I; 
	    J := fastPower(I,c);
	    not(squarefreeGens(J)=={})
	    )
	)
    )


-- Input: Ideal and List of variables to evaluate to 1
-- Output: Ideal with vars from list evaluated to 1
replaceVarsBy1 = method(TypicalValue => Ideal)
replaceVarsBy1(Ideal,List) := Ideal => (I,L) -> (
    w := flatten entries vars ring I;
    v := fold((i,o) -> replace(o,1,i),w,L);
    promote(substitute(I,matrix{v}),ring I)
    )


-- Input: Ideal and List of variables to evaluate to 0
-- Output: Ideal with vars from list evaluated to 0
replaceVarsBy0 = method(TypicalValue => Ideal)
replaceVarsBy0(Ideal,List) := Ideal => (I,L) -> (
    w := flatten entries vars ring I;
    v := fold((i,o) -> replace(o,0,i),w,L);
    promote(substitute(I,matrix{v}),ring I)
    )
    
-- Input: Monomial Ideal
-- Output: Boolean value determining if packed or not
isPacked = method(TypicalValue => Boolean)
isPacked(Ideal) := Boolean => I -> (
    d := # flatten entries vars ring I; 
    s := subsets(d);
    w := flatten(table(s,s,(a,b) -> {a,b}));
    w = select(w, i -> unique(join(i_0,i_1))==join(i_0,i_1));
    all(w,x -> isKonig(replaceVarsBy1(replaceVarsBy0(I,x_0),x_1)))
    )


noPackedSub = method(TypicalValue => List)
noPackedSub(Ideal) := List => I -> (if not(isKonig(I)) then "The ideal itself is not Konig!" else (
    var := flatten entries vars ring I; d := # var;
    s := delete({},subsets(d));
    w := flatten(table(s,s,(a,b) -> {a,b}));
    w = select(w, i -> unique(join(i_0,i_1))==join(i_0,i_1));
    firstFailure := select(1,w,x -> not(isKonig(replaceVarsBy1(replaceVarsBy0(I,x_0),x_1))));
    firstFailure = flatten firstFailure;
    varsReplacedBy0 := firstFailure_0;
    varsReplacedBy0 = var_(varsReplacedBy0);
    varsReplacedBy1 := firstFailure_1;
    varsReplacedBy1 = var_(varsReplacedBy1);
    varsReplacedBy0 = apply(apply(varsReplacedBy0,toString),i -> concatenate(i,"=>0"));
    varsReplacedBy1 = apply(apply(varsReplacedBy1,toString),i -> concatenate(i,"=>1"));
    varsReplacedBy0 | varsReplacedBy1))


noPackedAllSubs = method(TypicalValue => List)
noPackedAllSubs(Ideal) := List => I -> (var := flatten entries vars ring I; d := # var;
    s := delete({},subsets(d));
    w := flatten(table(s,s,(a,b) -> {a,b}));
    w = select(w, i -> unique(join(i_0,i_1))==join(i_0,i_1));
    allFailures := select(w,x -> not(isKonig(replaceVarsBy1(replaceVarsBy0(I,x_0),x_1))));
    allSubs := apply(allFailures, 
	o -> apply(var_(o_0),i->concatenate(toString i,"=>0")) | apply(var_(o_1),i->concatenate(toString i,"=>1")));
    if allSubs == {} then "Only I is not Konig -- all proper substitutions are Konig." else
    allSubs)
    


---------------------------------
---Symbolic Defect
---------------------------------

symbolicDefect = method(TypicalValue => ZZ, Options => {UseMinimalPrimes => false})
symbolicDefect(Ideal,ZZ) := opts -> (I,n) -> (
    R := ring I;
    Y := fastPower(I,n);
    S := R/Y;
    F := map(S,R);
    X := symbolicPower(I,n, UseMinimalPrimes => opts.UseMinimalPrimes);
    # flatten entries mingens F(X)
      )



-----------------------------------------------------------
-----------------------------------------------------------
-- Functions for asymptotic invariants
-----------------------------------------------------------
-----------------------------------------------------------

-- Computes the symbolic polyhedron for a monomial ideal
-- Input: an ideal or a  monomial ideal 
-- Output: a Polyhedron

symbolicPolyhedron = method();

symbolicPolyhedron Ideal := Polyhedron => I -> (
if not isMonomial(I) then ( 
    print "Error -- symbolicPolyhedron cannot be applied for an ideal that is not monomial"; 
    return
    );   
return symbolicPolyhedron monomialIdeal I
)


symbolicPolyhedron MonomialIdeal := Polyhedron => I -> ( 
Pd:=primaryDecomposition I;
P:=apply(Pd, a-> radical a);
maxP:={};
apply(P, a-> if #select(P, b-> isSubset(a,b))==1 then maxP=maxP|{a});
Q:=for p in maxP list (intersect select(Pd, a-> isSubset(a,p)));
PI:=apply(Q, a-> newtonPolytope sum flatten entries gens a);
C := posHull id_(ZZ^(dim ring I));
QI :=apply(PI, p-> p+C);
N :=intersection QI;
return N
)

alpha = I -> min apply(flatten entries gens I, f-> (degree f)_0) 

-- Computes the Waldschmidt constant for a given ideal
waldschmidt = method(Options=>{SampleSize=>10});
waldschmidt Ideal := opts -> I -> (
if isMonomial I then ( 
    print "Ideal is monomial, the Waldschmidt constant is computed exactly";   
    N:=symbolicPolyhedron I;
    return min apply (entries transpose vertices N, a-> sum  a)
    )
else (
    print ("Ideal is not monomial, the  Waldschmidt constant is approximated using first "| opts#SampleSize |" powers.");
    return min for i from 1 to opts#SampleSize  list alpha(symbolicPower(I,i))/i
    )
)

waldschmidt MonomialIdeal := opts -> I -> (  
    N:=symbolicPolyhedron I;
    return min apply (entries transpose vertices N, a-> sum  a)
    )

lowerBoundResurgence = method(TypicalValue => QQ, Options =>{UseWaldschmidt=>false})
lowerBoundResurgence(Ideal, ZZ) := opts  -> (I,m) -> (
    l := max append(apply(toList(2 .. m),o -> (containmentProblem(I,o)-1)/o),1);
    if opts#UseWaldschmidt == false then return l
    else return max {l, alpha(I)/waldschmidt(I)}
    )


-- for this function I am assuming that the asymptotic regularity is an infimum
-- this is more specific than being a limit
-- I need to think if this is true (did not find it written in the literature)

asymptoticRegularity = method(Options=>{SampleSize=>10});
asymptoticRegularity Ideal := opts -> I -> (
    print ("The asymptotic regularity is approximated using first "| opts#SampleSize |" powers.");
    return min for i from 1 to opts#SampleSize  list regularity(symbolicPower(I,i))/i
    ) 





-----------------------------------------------------------
-----------------------------------------------------------
--Documentation
-----------------------------------------------------------
-----------------------------------------------------------

beginDocumentation()

document { 
  Key => SymbolicPowers,
  Headline => "A package for computing symbolic powers of ideals",
   
   "This package gives the ability to compute symbolic powers, and related invarients,
   of ideals in a polynomial ring or a quotient of a polynomial ring. For example, 
   in the context of the default behavoir, ", TO "symbolicPower", " assumes the 
   following definition of the symbolic power of an ideal ", TEX /// I ///, ",", 
   TEX /// $$I^{(n)} = \cap_{p \in Ass(R/I)}(I^nR_p \cap R ),$$ ///,
   "as defined by M. Hochster and C. Huneke.",

   PARA {"Alternatively, as defined in Villarreal, ", TO "symbolicPower", 
       " has the option to restrict to minimal primes versus use all associated 
       primes with ", TO "UseMinimalPrimes", ".", "In particular, the 
       symbolic power of an ideal ", TEX ///I ///, " is defined as", 
       TEX /// $$I^{(n)} = \cap_{p \in Min(R/I)}(I^nR_p \cap R ),$$ ///, 
       "where ", TEX /// Min(R/I)///, " is the set of minimal primes in ", 
       TEX /// I ///, "."},
   
   UL { 
       {"M. Hochster and C. Huneke.", EM " Comparison of symbolic and ordinary powers of ideals.", 
	   " Invent. Math. 147 (2002), no. 2, 349–369."}, 
       {"R. Villarreal.", EM " Monomial algebras.", " Second edition. Monographs and Research Notes 
	   in Mathematics. CRC Press, Boca Raton, FL, 2015. xviii+686 pp. ISBN: 978-1-4822-3469-5."}, 
       {"Hailong Dao, Alessandro De Stefani, Eloísa Grifo, Craig Huneke, and Luis Núñez-Betancourt.", 
	   EM "Symbolic powers of ideals", ", ", HREF("https://arxiv.org/abs/1708.03010","https://arxiv.org/abs/1708.03010")} 
       },
  
   SUBSECTION "Contributors", "The following people have generously
   contributed code or worked on our code at various Macaulay2
   workshops.",
     
     UL {
	 "Ben Drabkin",
	 "Alexandra Seceleanu",
	 "Branden Stone"
	},

   SUBSECTION "A Quick Introduction",
   UL {
    TO "Computing symbolic powers of an ideal",
    TO "Alternative algorithm to compute the symbolic powers of a prime ideal in positive characteristic"
    },
    
 
  SUBSECTION "Other Related Examples",
  UL {
    TO "The Containment Problem",
    TO "Sullivant's algorithm for primes in a polynomial ring",
    TO "Monomial Curves",
    TO "The Packing Problem"    
  }

}  



doc ///
     Key
     	  "A quick introduction to this package"
     Headline
     	  How to use this package
     Description
     	  Text
	       Here is a list of some examples which illustrate various parts of this package.
	       
	       {\bf First examples which show how to use this package}
    	       
	       $\bullet$ @TO"Computing symbolic powers of an ideal"@
	       
	       $\bullet$ @TO"Alternative algorithm to compute the symbolic powers of a prime ideal in positive characteristic"@
 
               {\bf Other examples which illustrate this package}

               $\bullet$ @TO"The Containment Problem"@
	       
	       $\bullet$ @TO"Sullivant's algorithm for primes in a polynomial ring"@
	       
	       $\bullet$ @TO"Monomial curves"@
    	       	     
	       {\bf The Packing Problem}
	       
	       $\bullet$ @TO"The Packing Problem"@
	       
 	  	  
///

doc ///
     Key
     	  "Computing symbolic powers of an ideal"
     Description
     	 Text
	      Given an ideal, symbolicPower computes a given symbolic power.  
	 Example     
	      B = QQ[x,y,z];
	      I = ideal(x*(y^3-z^3),y*(z^3-y^3),z*(x^3-y^3));
	      J = symbolicPower(I,3)
     Description
         Text
              Various algorithms are used, in the following order:     
	      
	      1. If $I$ is a homogeneous ideal in a polynomial ring whose height is one less than the dimension of the ring, returns the saturation of $I$; 
	      
	      2. If $I$ is squarefree monomial ideal, intersects the powers of the associated primes of $I$'
	      
	      3. If $I$ is monomial ideal, but not squarefree, takes an irredundant primary decomposition of $I$ and intersects the powers of those ideals;
	      
	      4. If $I$ is prime, computes a primary decomposition of $I^n$ and intersects the components with radical $I$.
	      
	      5. If all else fails, compares the radicals of a primary decomposition of $I^n$ with the associated primes of $I$, and intersects the unmixed components.
///



doc ///
     Key
     	  "Alternative algorithm to compute the symbolic powers of a prime ideal in positive characteristic"
     Description
     	 Text
	      Given a prime ideal P in a regular ring of positive characteristic, symbPowerPrimePosChar computes its symbolic powers. Unfortunately, this algorithm is slower than others.  
	      
	 Example     
	      R = ZZ/7[x,y,z]
	      P = ker map(ZZ/7[t],R,{t^3,t^4,t^5})
	      J = symbPowerPrimePosChar(P,2)
	 Text
	      The symbolic powers of P do not coincide with its powers.
	 Example     
	      J == P^2
	 Text
	      We can also test it a bit faster, without computing the symbolic powers of P:
	 Example
	      isSymbolicEqualOrdinary(P,2)

///



doc ///
     Key
     	  "The Containment Problem"
     Description
     	 Text
	      Given an ideal I, we can determine if $I^{(m)} \subseteq I^n$. For example, here is an ideal that fails the containment $I^{(3)} \subseteq I^2$:
	 Example     
	      B = ZZ/101[x,y,z];
	      I = ideal(x*(y^3-z^3),y*(z^3-x^3),z*(x^3-y^3));
	      isSymbPowerContainedinPower(I,3,2)
     	 Text
	      We can also determine the smallest symbolic power contained in a given power.
     	 Text
	      In our example, $I^{(4)}$ is the smallest symbolic power contained in $I^2$:
	 Example
	      containmentProblem(I,2)
     	 Text
	      We can ask the same question backwards: what is the largest power of I that contains $I^{(4)}$?
	 Example
	      containmentProblem(I,4,InSymbolic => true)     
///



doc ///
     Key
     	  "Sullivant's algorithm for primes in a polynomial ring"
     Description
     	 Text
	      Given ideals I and J in a polynomial ring, we compute their join I*J:  
	 Example     
	      S = QQ[x,y,z];
	      I = ideal(x^3,x^2*y^2,x*z^3,y^4,y^2*z);
	      J = joinIdeals(I,I)
     	 Text
	      Following Seth Sullivant's "Combinatorial symbolic powers", J. Algebra 319 (2008), no. 1, 115--142, we can compute symbolic powers of prime ideals using join:
	 Example     
	      A = QQ[x,y,z];
	      symbolicPowerJoin(ideal(x,y),2)  
       	 Example
	      f = map(QQ[t],A,{t^3,t^4,t^5})
	      P = ker f;
	      symbolicPowerJoin(P,2)
///



doc ///
     Key
     	  "Monomial Curves"
     Description
     	 Text
	      To test containments of symbolic and ordinary powers of ideals defining monomial curves, we can skip the step where we define the ideals.
     	 Text
	      For example, if I is the ideal defining the monomial curve defined by $t^3, t^4, t^5$ over $\mathbb{Z}/101$, we can ask whether $I^{(3)} \subseteq I^2$:
	 Example     
	      symbolicContainmentMonomialCurve(ZZ/101,{3,4,5},3,2)
     	 Text
	      Or we simply ask for the symbolic powers of these ideals. For example, here is the third of the same ideal:
	 Example     
	      symbolicPowerMonomialCurve(ZZ/101,{3,4,5},3)
///



doc ///
     Key
     	  "The Packing Problem"
     Description
     	 Text
	      Given a square-free monomial ideal I of codimension c, I is Konig if it contains a regular sequence of monomials of length c.
     	 
	      We can test if a given ideal is Konig:
	 Example     
	      R = QQ[x,y,z]
	      I = ideal(x*y,z*y,x*z)
	      isKonig(I)
     	 Text
	      I is said to have the packing property if any ideal obtained from I by setting any number of variables equal to 0 is Konig.
	 Example     
	      isPacked(I)
     	 Text
	      Given an ideal that is not packed, we can determine which variable substitutions lead to ideals that are not Konig.
	 Example     
	      noPackedAllSubs(I)
     	 Text
	      We can obtained just one substitution leading to an ideal that is not Konig, or all such substitutions:
	 Example     
	      R = QQ[a,b,c,d,A,B,C,D]
	      J = ideal"ABCD,cdAB,abcD,bcABD,abcBD,abcdA,abcAD,abdAC,acdBC,acBCD,abcdC,bcdAC,bcACD,bcdAD,acdBD,adBCD,acABD,bdABC,adABC"
	      isPacked(J)
	      noPackedSub(J)
     	 Text
	      These can easily be tested:
	 Example     
	      L = substitute(J,matrix{{1,0,c,d,A,1,C,D}})
	      isKonig(L)

///




doc ///
   Key
       bigHeight
       (bigHeight, Ideal)
   Headline
       Big height of an ideal: the largest height of an associated prime
   Usage
       bigHeight(I)
   Inputs
        I:Ideal
   Outputs
       :ZZ
           the largest height of an associated prime of I
   Description
       Text  
           The algorithm is based on the following result by Eisenbud-Huneke-Vasconcelos, 
	   in their 1993 Inventiones Mathematicae paper:
	   $\bullet$ codim $Ext^d(M,R) \geq d$ for all d
	   $\bullet$ If P is an associated prime of M of codimension d := codim P > codim M, 
	   then codim $Ext^d(M,R) = d$ and the annihilator of $Ext^d(M,R)$ is contained in P
	   $\bullet$ If codim $Ext^d(M,R) = d$, then there really is an associated prime of codimension d.
       Example
           R = QQ[x,y,z,a,b]
     	   J = intersect(ideal(x,y,z),ideal(a,b))
    	   bigHeight(J)
   SeeAlso
       codim
///


doc ///
   Key
       assPrimesHeight
       (assPrimesHeight, Ideal)
   Headline
       The heights of all associated primes
   Usage
       assPrimesHeight(I)
   Inputs
        I:Ideal
   Outputs
       :List
           the heights of all associated primes of I
   Description
       Text  
           The algorithm is based on the following result by Eisenbud-Huneke-Vasconcelos, 
	   in their 1993 Inventiones Mathematicae paper:
	   
	   $\bullet$ codim $Ext^d(M,R) \geq d$ for all d
	   
	   $\bullet$ If P is an associated prime of M of codimension d := codim P > codim M, 
	   then codim $Ext^d(M,R) = d$ and the annihilator of $Ext^d(M,R)$ is contained in P
	   
	   $\bullet$ If codim $Ext^d(M,R) = d$, then there really is an associated prime of codimension d.
	   
       Example
           R = QQ[x,y,z,a,b]
     	   J = intersect(ideal(x,y,z),ideal(a,b))
    	   assPrimesHeight(J)
   SeeAlso
       bigHeight
       codim
///


doc ///
   Key
       isSymbPowerContainedinPower
       (isSymbPowerContainedinPower, Ideal, ZZ, ZZ)
   Headline
       Tests if the m-th symbolic power an ideal is contained the n-th in a power
   Usage
       isSymbPowerContainedinPower(I,m,n)
   Inputs
        I:Ideal
    	m:ZZ
    	n:ZZ
   Outputs
       :Boolean
           whether the m-th symbolic power of 'I' is contained in the n-th power
   Description
       Example
           R = QQ[x,y,z]
     	   J = ideal(x,y)
    	   isSymbPowerContainedinPower(J,3,2)
   SeeAlso
       containmentProblem
///


doc ///
   Key
       containmentProblem
       (containmentProblem, Ideal, ZZ)
   Headline
       Given an ideal I and an integer n, returns the order of the smallest symbolic power of I contained in I^n.
   Usage
       containmentProblem(I,n)
   Inputs
	I:Ideal
	n:ZZ
   Outputs
       :ZZ
           the minimum value m such that the m-th symbolic power of I is contained in I^n
   Description
       Example
	   B = QQ[x,y,z];
	   f = map(QQ[t],B,{t^3,t^4,t^5})
	   I = ker f;
	   m = containmentProblem(I,2)
   SeeAlso
       isSymbPowerContainedinPower
///

--To delete and include in containmentProblem
///
   Key
       containmentProblemGivenSymbolicPower
       (containmentProblemGivenSymbolicPower, Ideal, ZZ)
   Headline
       Given an ideal I and an integer n, returns the order of the largest power of I containing in I^{(n)}.
   Usage
       containmentProblemGivenSymbolicPower(I,m)
   Inputs
	I:Ideal
	m:ZZ
   Outputs
       :ZZ
           the largest value n such that I^n contains the m-th symbolic power of I.
   Description
       Example
	   B = QQ[x,y,z];
	   f = map(QQ[t],B,{t^3,t^4,t^5})
	   I = ker f;
	   containmentProblemGivenSymbolicPower(I,3)
   SeeAlso
       containmentProblem
///

doc ///
   Key
       frobeniusPower
       (frobeniusPower, Ideal, ZZ)
   Headline
       Given an ideal I in characteristic p and q=p^e, returns the q-th Frobenius power of I.
   Usage
       frobeniusPower(I,q)
   Inputs
	I:Ideal
	q:ZZ
   Outputs
       :Ideal
           the q-th Frobenius power of I
   Description
       Example
	   B = ZZ/7[x,y,z];
	   f = map(ZZ/7[t],B,{t^3,t^4,t^5})
	   I = ker f;
	   frobeniusPower(I,7)
///

doc ///
   Key
       symbPowerPrimePosChar
       (symbPowerPrimePosChar, Ideal, ZZ)
   Headline
       Given an ideal I in a polynomial ring over a field of positive characteristic, and an integer n, returns the n-th symbolic power of I contained.
   Usage
       	symbPowerPrimePosChar(I,n)
   Inputs
        I:Ideal
	n:ZZ
   Outputs
       :Ideal
           the n-th symbolic power of I
   Description
       Text  
           To compute $I^{(a)}$, find the largest value k with $q = p^k \leq a$. Then $I^{(a)} = (I^{[q]} : I^{a-q+1})$.
       Example 
           B = ZZ/7[x,y,z];
	   f = map(ZZ/7[t],B,{t^3,t^4,t^5})
	   I = ker f;
	   symbPowerPrimePosChar(I,2)
   SeeAlso
       symbolicPower
///



doc ///
   Key
       symbolicPower
       (symbolicPower, Ideal, ZZ)
   Headline
       Given an ideal I and an integer n, returns the n-th symbolic power of I.
   Description
       Text
              Various algorithms are used, in the following order:     
	      
	      1. If $I$ is a homogeneous ideal in a polynomial ring whose height is one less than the dimension of the ring, returns the saturation of $I$; 
	      
	      2. If $I$ is squarefree monomial ideal, intersects the powers of the associated primes of $I$'
	      
	      3. If $I$ is monomial ideal, but not squarefree, takes a primary decomposition of $I$, picks the maximal elements in it, and intersects their powers;
	      
	      4. If $I$ is prime, computes a primary decomposition of $I^n$ and intersects the components with radical $I$.
	      
	      5. If all else fails, compares the radicals of a primary decomposition of $I^n$ with the associated primes of $I$, and intersects the unmixed components.
   Usage
       	symbolicPower(I,n)
   Inputs
        I:Ideal
	n:ZZ
   Outputs
       :Ideal
           the n-th symbolic power of I
   Description
       Example
              B = QQ[x,y,z];
	      f = map(QQ[t],B,{t^3,t^4,t^5})
	      I = ker f;
	      symbolicPower(I,2)
   SeeAlso
      symbPowerPrimePosChar
///



doc ///
   Key
       isSymbolicEqualOrdinary
       (isSymbolicEqualOrdinary, Ideal, ZZ)
   Headline
       Given a radical ideal I and an integer n, returns true if and only if $I^n=I^{(n)}$.
   Usage
       	isSymbolicEqualOrdinary(I,n)
   Inputs
        I:Ideal
	n:ZZ
   Outputs
       :Boolean
           the truth value of $I^n==I^{(n)}$
   Description
       Text
              Circumvents computing the symbolic powers in most cases, by first testing the bigheigh of $I^n$
       Example
              B = QQ[x,y,z];
	      f = map(QQ[t],B,{t^3,t^4,t^5})
	      I = ker f;
	      isSymbolicEqualOrdinary(I,2)
   SeeAlso
      isSymbPowerContainedinPower
///



doc ///
   Key
       joinIdeals
       (joinIdeals,Ideal,Ideal)
   Headline
       Computes the join of the given ideals
   Usage
       joinIdeals(Ideal,Ideal)
   Inputs
        I:Ideal
	J:Ideal
   Outputs
       :Ideal
 --          the join of I and J
   Description
       Text    
           See Seth Sullivant's "Combinatorial symbolic powers", J. Algebra 319 (2008), no. 1, 115--142, for a definition.
       Example
           S = QQ[x,y,z];
	   I = ideal(x^3,x^2*y^2,x*z^3,y^4,y^2*z);
	   J = joinIdeals(I,I)
///


doc ///
     Key 
         symbolicPowerJoin
	 (symbolicPowerJoin,Ideal,ZZ)
     Headline 
         Symbolic powers of prime ideals using Sullivant's algorithm.
     Usage 
         symbolicPowerJoin(P,n)
     Inputs 
	  P:Ideal
	  n:ZZ
     Outputs
          :Ideal
--  the n-th symbolic power of P
     Description	  
       Text
	   Computes the n-th symbolic power of the prime ideal P, using join of ideals.
	   
	   This is the algorithm in Seth Sullivant's "Combinatorial symbolic powers", J. Algebra 319 (2008), no. 1, 115--142.
       Example 
	   A = QQ[x,y,z];
	   symbolicPowerJoin(ideal(x,y),2) 
     SeeAlso 
	  joinIdeals
/// 




doc ///
     Key 
         symbolicContainmentMonomialCurve
	 (symbolicContainmentMonomialCurve,List,ZZ,ZZ)
	 (symbolicContainmentMonomialCurve,Ring,List,ZZ,ZZ)
     Headline 
         Tests the containment of symbolic in ordinary powers of ideals for monomial curves.
     Usage 
         symbolicContainmentMonomialCurve(L,m,n)
	 symbolicContainmentMonomialCurve(k,L,m,n)
     Inputs 
     	  k:Ring
	  L:List
	  m:ZZ
	  n:ZZ
     Outputs
          :Boolean
     Description	  
       Text
	   Tests whether $I^{(m)} \subseteq I^n$, where $I$ is the defining ideal for the monomial curve defined by $t^{a_1}, \ldots, t^{a_n}$. If no field is provided, the ideal is defined over $\mathbb{Q}$.
       Example 
	   symbolicContainmentMonomialCurve({3,4,5},3,2) 
     SeeAlso 
	  isSymbPowerContainedinPower
	  symbolicPowerMonomialCurve
/// 



doc ///
     Key 
         symbolicPowerMonomialCurve
	 (symbolicPowerMonomialCurve,List,ZZ)
	 (symbolicPowerMonomialCurve,Ring,List,ZZ)
     Headline 
         Computes the symbolic powers of ideals defining monomial curves.
     Usage 
         symbolicPowerMonomialCurve(L,m)
	 symbolicPowerMonomialCurve(k,L,m)
     Inputs 
     	  k:Ring
	  L:List
	  m:ZZ
     Outputs
          :Ideal
     Description	  
       Text
	   Finds the m-th symbolic power of I, where I is the defining ideal for the monomial curve defined by $t^{a_1}, \ldots, t^{a_n}$. If no field is provided, the ideal is defined over $\mathbb{Q}$.
       Example 
	   symbolicPowerMonomialCurve({3,4,5},3) 
     SeeAlso 
	  containmentProblem
/// 




doc ///
     Key 
         squarefreeGens
	 (squarefreeGens,Ideal)
     Headline 
         Returns all square-free monomials in a minimal generating set of the given ideal.
     Usage 
         squarefreeGens(I)
     Inputs 
     	  I:Ideal
     Outputs
          :List
     Description	  
       Text
	   Given a monomial ideal I, returns all square-free monomials in a minimal generating set of I.
       Example 
	   R = QQ[x,y,z];
	   I = ideal(x*y,y*z,x^2);
	   squarefreeGens(I) 
     SeeAlso 
	  squarefreeInCodim
/// 

doc ///
     Key 
         squarefreeInCodim
	 (squarefreeInCodim,Ideal)
     Headline 
         Finds square-fee monomials in I^c, where c is the codimension of the given ideal.
     Usage 
         squarefreeInCodim(I)
     Inputs 
     	  I:Ideal
     Outputs
          :List
     Description	  
       Text
	   Given a monomial ideal I, returns all square-free monomials in a minimal generating set of I^c.
       Example 
	   R = QQ[x,y,z];
	   I = ideal(x*y,y*z,x*z);
	   squarefreeInCodim(I) 
     SeeAlso 
	  squarefreeGens
///



doc ///
     Key 
         isKonig
	 (isKonig,Ideal)
     Headline 
         Determines if a given square-free ideal is Konig.
     Usage 
         isKonig(I)
     Inputs 
     	  I:Ideal
     Outputs
          :Boolean
     Description	  
       Text
	   Given a square-free monomial ideal I, determines if the ideal is Konig.
       Text
	   A square-free monomial ideal I of codimension c is Konig if it contains a regular sequence of monomials of length c.
       Example 
	   R = QQ[x,y,z];
	   I = ideal(x*y,y*z,x*z);
	   isKonig(I) 
     SeeAlso 
	  squarefreeGens
///

doc ///
     Key 
         isPacked
	 (isPacked,Ideal)
     Headline 
         Determines if a given square-free ideal is packed.
     Usage 
         isPacked(I)
     Inputs 
     	  I:Ideal
     Outputs
          :Boolean
     Description	  
       Text
	   Given a square-free monomial ideal I, determines if the ideal is Konig.
       Text
	   A square-free monomial ideal I of codimension c is packed if every ideal obtained from it by replacing any number of variables by 1 or 0 is Konig.
       Example 
	   R = QQ[x,y,z];
	   I = ideal(x*y,y*z,x*z);
	   isPacked(I) 
     SeeAlso 
	  squarefreeGens
///


doc ///
     Key 
         noPackedSub
	 (noPackedSub,Ideal)
     Headline 
         Finds a substitution of variables by 1 and/or 0 for which I is not Konig.
     Usage 
         noPackedSub(I)
     Inputs 
     	  I:Ideal
     Outputs
          :List
     Description	  
       Text
	   Given an ideal that is not packed, returns a substitution of variables by 0 and/or 1 that produces an ideal that is not Konig.
       Text
	   Determines only one such substitutions, even though others may exist.
       Example 
	   R = QQ[x,y,z];
	   I = ideal(x*y,y*z,x*z);
	   noPackedSub(I) 
     SeeAlso 
	  isPacked	  
///
	  

doc ///
     Key 
         noPackedAllSubs
	 (noPackedAllSubs,Ideal)
     Headline 
         Finds all substitutions of variables by 1 and/or 0 for which I is not Konig.
     Usage 
         noPackedAllSubs(I)
     Inputs 
     	  I:Ideal
     Outputs
          :List
     Description	  
       Text
	   Given an ideal that is not packed, returns a list with all substitution of variables by 0 and/or 1 that produces an ideal that is not Konig.
       Example 
	   R = QQ[x,y,z];
	   I = ideal(x*y,y*z,x*z);
	   noPackedAllSubs(I) 
     SeeAlso 
	  noPackedSub
	  isPacked	  
///

doc ///
     Key 
         minDegreeSymbPower
	 (minDegreeSymbPower,Ideal,ZZ)
     Headline 
         Returns the minimal degree of a given symbolic power of an ideal.
     Usage 
         minDegreeSymbPower(Ideal,ZZ)
     Inputs 
     	  I:Ideal
	  n:ZZ
     Outputs
          :ZZ
     Description	  
       Text
	   Given an ideal $I$ and an integer $n$, returns the minimal degree of an element in $I^{(n)}$.
       Example 
	   T = QQ[x,y,z];
	   I = intersect(ideal"x,y",ideal"x,z",ideal"y,z")
	   minDegreeSymbPower(I,2)

///

doc ///
     Key 
         lowerBoundResurgence
	 (lowerBoundResurgence,Ideal,ZZ)
     Headline 
         Computes a lower bound for the resurgence of a given ideal
     Usage 
         lowerBoundResurgence(Ideal,ZZ)
     Inputs 
     	  I:Ideal
	  n:ZZ
     Outputs
          :QQ
     Description	  
       Text
	   Given an ideal $I$ and an integer $n$, finds the maximum of the quotiens m/k that fail $I^{(m)} \subseteq I^k$ with $k \leq n$.
       Example 
	   T = QQ[x,y,z];
	   I = intersect(ideal"x,y",ideal"x,z",ideal"y,z");
	   lowerBoundResurgence(I,5)

///

doc ///
     Key 
         UseWaldschmidt
     Headline 
         Optional input for computing a lower bound for the resurgence of a given ideal
     Usage 
         lowerBoundResurgence(Ideal,ZZ,UseWaldschmidt=>true)
     Inputs 
     	  I:Ideal
	  n:ZZ
     Outputs
          :QQ
     Description	  
       Text
	   Given an ideal $I$ and an integer $n$, returns the larger value between the 
	   maximum of the quotiens $m/k$ that fail $I^{(m)} \subseteq I^k$ with $k \leq n$ 
	   and $\frac{\alpha(I)}{waldschmidt(I)}$. 
       Example 
	   T = QQ[x,y,z];
	   I = intersect(ideal"x,y",ideal"x,z",ideal"y,z");
	   lowerBoundResurgence(I,5,UseWaldschmidt=>true)

///



doc ///
     Key 
         symbolicPolyhedron
	 (symbolicPolyhedron,Ideal)
	 (symbolicPolyhedron,MonomialIdeal)
     Headline 
         Computes the symbolic polyhedron for a monomial ideal. 
     Usage 
         symbolicPolyhedron(I)
     Inputs 
     	  I:Ideal
     Outputs
          :Polyhedron 
     Description	  
       Text
	   The symbolic polyhedron associated to a monomial ideal I is defined in the paper "Symbolic Powers of Monomial Ideals" 
	   by S. M. Cooper, R. J. D. Embree, H. T. Ha, A. H. Hoefel. The symbolic polyhedron contains the exponent vector of any
	   monomial in I^n scaled by 1/n.
	  
       Text
       	   This function uses the Polyhedra package and returns an object of type Polyhedron.
       
       Example 
	   R = QQ[x,y,z];
	   I = ideal(x*y,y*z,x*z);
	   symbolicPolyhedron(I)
        
     SeeAlso
	  Polyhedra
///

doc ///
     Key 
         waldschmidt
	 (waldschmidt,Ideal)
	 (waldschmidt,MonomialIdeal)
     Headline 
         Computes the Waldschmidt constant  for a homogeneous ideal. 
     Usage 
         waldschmidt(I)
     Inputs 
     	  I:Ideal
     Outputs
          :QQ 
     Description	  
       Text
	   The Waldschmidt constant for a homogeneous ideal I is defined as $waldschmidt(I)=lim_{n\to\infty} \frac{\alpha(I^{(n)})}{n}$, 
	   where $\alpha(J)$ denotes the smallest degree of a nonzero element in a given homogeneous ideal $J$. The limit of the sequence 
	   $\frac{\alpha(I^{(n)})}{n}$ exists because of the subadditivity of $\alpha$ and is equal to the infimum of the sequence $\frac{\alpha(I^{(n)})}{n}$.
	  
       Text
       	   The Waldschmidt constant can be computed for monomial ideals as the smallest value of the sum of the coordinates over all the points of 
	   the symbolic polyhedron. The function uses this method to return an exact answer for the Waldschmidt constant of a monomial ideal.
	   
       Text
       	   For ideals that are not monomial, we give an approximation of the Waldschmidt constant by taking the minimum value of $\frac{\alpha(I^{(n)})}{n}$
	   over a finite number of exponents $n$, namely for $n$ from 1 to the optional parameter SampleSize.  
       
       Example 
	   R = QQ[x,y,z];
	   I = ideal(x*y,y*z,x*z);
	   waldschmidt(I)
	   
       Example 
	   R = QQ[x,y,z];
	   J = ideal (x*(y^3-z^3),y*(z^3-x^3),z*(x^3-y^3));
	   waldschmidt(J, SampleSize=>5)
        
     SeeAlso 
	  symbolicPolyhedron
///


doc ///
     Key 
         SampleSize
     Headline 
         An optional parameter used for approximating asymptotic invariants that are defined as limits.
     Usage 
         waldschmidt(I,SampleSize=>ZZ)
     Description	  
         Text
       	   For ideals that are not monomial, we give an approximation of the Waldschmidt constant by taking the minimum value of $\frac{\alpha(I^{(n)})}{n}$
	   over a finite number of exponents $n$, namely for $n$ from 1 to the optional parameter SampleSize. Similarly the SampleSize is used to give an
	   approximation for the asymptotic regularity by computing the smallest value of $\frac{reg(I^{(n)})}{n}$ for $n$ from
	   1 to the SampleSize.
     
         Example
           R = QQ[x,y,z];
	   J = ideal (x*(y^3-z^3),y*(z^3-x^3),z*(x^3-y^3));
	   waldschmidt(J, SampleSize=>5)
///	   


doc ///
     Key 
         InSymbolic
     Headline 
         An optional parameter used in containmentProblem
     Usage 
         containmentProblem(I,n,InSymbolic => true)
     Description	  
         Text
       	   Given an ideal I and an integer n, InSymbolic is used to ask the following question:
	   What is the largest power cointained in the symbolic power $I^{(n)}$?
         Example
           R = QQ[x,y,z];
	   J = ideal (x*(y^3-z^3),y*(z^3-x^3),z*(x^3-y^3));
	   containmentProblem(J,3,InSymbolic => true)
///	   
	   
doc ///
     Key 
         asymptoticRegularity
     Headline 
         An asymptotic invariant defined as the limit of the regularity of the symbolic powers scaled by the symbolic exponent.
     Usage 
         asymptoticRegularity(I,SampleSize=>ZZ)
     Description
         Text	  
       	   We give an approximation of the asymptotic regularity by taking the minimum value of $\frac{reg(I^{(n)})}{n}$
	   over a finite number of exponents $n$, namely for $n$ from 1 to the optional parameter SampleSize.  
     
         Example
           R = QQ[x,y,z];
	   J = ideal (x*(y^3-z^3),y*(z^3-x^3),z*(x^3-y^3));
	   asymptoticRegularity(J, SampleSize=>5)
///

doc ///
   Key
         symbolicDefect
        (symbolicDefect, Ideal, ZZ)
   Headline
         Given an ideal I and integer m, returns the size of a minimal generating set for the m-th symbolic power of I modulo I^m.
   Usage
         symbolicDefect(I,m)
   Inputs
         I:Ideal
         m:ZZ
   Outputs
          :ZZ
             the size of a minimal generating set of the m-th symbolic power of I modulo I^m.
   Description
       Example
         R = QQ[x,y,z]    
         I = ideal(x*y,x*z,y*z);					      
	 symbolicDefect(I,2)
 ///


TEST ///
   S = QQ[x,y,z];
   I = ideal(x,y,z);
   assert(isSymbPowerContainedinPower(I,2,2) == true)
///

--bigHeight
TEST ///
R=ZZ/2[x,y,z]
I=ideal(x,y)
assert(bigHeight(I)==2)
///

TEST ///
R=QQ[x,y,z]
I=ideal(x,y^3,z^2)
assert(bigHeight I==3)
///


TEST ///
R=QQ[x,y,z]
I=ideal(x*(y^3-z^3),y*(z^3-x^3),z*(x^3-y^3))
assert(bigHeight(I)==2)
///


--symbolicPower
TEST ///
R=QQ[x,y,z]
I=ideal(y-z,x+z)
assert(symbolicPower(I,2)==ideal(y^2-2*y*z+z^2,x*y-x*z+y*z-z^2,x^2+2*x*z+z^2))
///

TEST ///
R=QQ[x,y,z]
I=ideal(x)
assert(symbolicPower(I,2)==ideal(x^2))
///

TEST ///
R=QQ[x,y,z]
I=ideal(x+1)
assert(symbolicPower(I,2)==ideal(x^2+2*x+1))
///

TEST ///
R=QQ[w,x,y,z]
I=ideal(x*y+1,w*y*z)
assert(symbolicPower(I,3)==ideal(w^3*z^3,w^2*x*y*z^2+w^2*z^2,w*x^2*y^2*z+2*w*x*y*z+w*z,x^3*y^3+3*x^2*y^2+3*x*y+1))
///

TEST ///
R = QQ[x,y,z]
I = ideal"x,y"
assert(symbolicPower(I,2)==I^2)
///


TEST ///
R=QQ[x,y,z]
I=ideal(x*y+x*z)
assert(symbolicPower(I,2)==ideal((x*y+x*z)^2))
///

--isSymbPowerContainedinPower
TEST ///
R=QQ[x,y];

I=ideal(x);

assert(isSymbPowerContainedinPower(I,2,3)==false)
///

TEST ///
R=QQ[x,y];

I=ideal(x);

assert(isSymbPowerContainedinPower(I,2,2)==true)
///

TEST ///
R=QQ[x,y];

I=ideal(x);

assert(isSymbPowerContainedinPower(I,3,2)==true)
///

--ContainmentProblem

TEST ///
R=QQ[x,y,z];

I=ideal(x*y,x*z,y*z);

assert(containmentProblem(I,2)==3)
///

TEST ///
R=QQ[x,y,z]
I=ideal(x*(y^3-z^3),y*(z^3-x^3),z*(x^3-y^3))
assert(containmentProblem(I,2)==4)
///

--frobeniusPower
TEST ///
R=ZZ/3[x,y]
I=ideal(x*y^2+1,x^2)
assert(frobeniusPower(I,9)==ideal(x^9*y^(19)+1,x^(18)))
///

--lowerBoundResurgence
TEST ///
R=QQ[x,y,z]
I=ideal(x*y,x*z,y*z)
assert(lowerBoundResurgence(I,5)==6/5)
///

----isSymbolicEqualOrdinary
TEST ///
R=QQ[x,y,z]
I=ideal(x*y,x*z,y*z)
assert(isSymbolicEqualOrdinary(I,2)==false)
///

TEST ///
R=ZZ/3[x,y]
I=ideal(x)
assert(isSymbolicEqualOrdinary(I,3)==true)
///

TEST ///
R=QQ[x,y,z]
I=ideal(x*z,y*z)
assert(isSymbolicEqualOrdinary(I,2)==true)
///

----joinIdeals
TEST ///
R=QQ[x,y,z]
I=ideal(x,y)
J=ideal(x,z)
assert(joinIdeals(I,J)==ideal(x))
///

----symbolicPowerJoin

----containmentProblem given Symbolic Power
TEST ///
R=QQ[x,y,z]
I=ideal(x*(y^3-z^3),y*(z^3-x^3),z*(x^3-y^3))
assert(containmentProblem(I,4,InSymbolic => true)==2)
///

----symbolicContainmentMonomialCurve
TEST ///
R=QQ[x,y,z]
assert(symbolicContainmentMonomialCurve({1,2,3},4,5)==false)
///

TEST ///
R=QQ[x,y,z]
assert(symbolicContainmentMonomialCurve({1,2,3},5,4)==true)
///

TEST ///
assert(symbolicContainmentMonomialCurve(QQ[w,x,y,z],{2,3},3,2)==true)
///
----squarefreeGens
TEST ///
R=ZZ/5[w,x,y,z]
I=ideal(y^2*z,x*y*w,z*w^3)
assert(squarefreeGens(I)=={w*x*y})
///

TEST ///
R=QQ[x,y,z]
I=ideal(x^2*z,x*y^8,z^3)
assert(squarefreeGens(I)=={})
///

----squarefreeInCodim
TEST ///
R=QQ[x,y,z]
I=ideal(x,y^2)
assert(squarefreeInCodim I=={})
///

TEST ///
R=ZZ/2[x,y,z]
I=ideal(x,y)
assert(squarefreeInCodim I=={x*y})
///

----symbolicPowerMonomialCurve
TEST ///
I= symbolicPowerMonomialCurve({1,2,1},2)
R=ring I
assert(I==ideal(R_0^2-2*R_0*R_2+R_2^2,R_0*R_2^2-R_2^3-R_0*R_1+R_1*R_2,R_2^4-2*R_1*R_2^2+R_1^2))
///

-- symbolicPolyhedron
TEST ///
 R = QQ[x,y,z];
 I = ideal(x*y,y*z,x*z);
 -- assert((vertices symbolicPolyhedron I)== matrix{{1,1,0,1/2},{1,0,1,1/2},{0,1,1,1/2}})
///

-- waldschmidt
TEST ///
 R = QQ[x,y,z];
 I = ideal(x*y,y*z,x*z);
 assert(waldschmidt(I)==3/2)
///


----isKonig
TEST ///
R=ZZ/17[x]
I=ideal(1_R)
assert(isKonig(I)==true)
///

TEST ///
R=QQ[y,z]
I=ideal(0_R)
assert(isKonig(I)==true)
///

TEST ///
R=QQ[x,y,z]
I=ideal(x*y,x*z,y*z)
assert(isKonig(I)==false)
///

----isPacked

TEST ///
R=QQ[x,y,z]
I=ideal(x*y,x*z,y*z)
assert(isPacked(I)==false)
///


TEST ///
R=QQ[x,y,z,a,b]
I=intersect(ideal(x,y),ideal(x,z),ideal(z,a),ideal(y,a),ideal(x,b))
assert(isPacked(I)==true)
///

----noPackedSub
TEST ///
R=QQ[x,y,z]
I=ideal(x*y,x*z,y*z)
assert(noPackedSub(I)=="The ideal itself is not Konig!")
///


----noPackedAllSubs
TEST ///
R=QQ[x,y,z]
I=ideal(x*y,x*z,y*z)
assert(noPackedAllSubs I=="Only I is not Konig -- all proper substitutions are Konig.")
///

TEST ///
R=QQ[x_1..x_6]
I=intersect(ideal(x_1,x_2),ideal(x_2,x_3),ideal(x_3,x_1),ideal(x_3,x_4),ideal(x_4,x_5),ideal(x_5,x_6),ideal(x_6,x_4))
assert(noPackedAllSubs I=={{"x_1=>0", "x_2=>1", "x_3=>1"}, {"x_2=>0", "x_1=>1", "x_3=>1"}, {"x_5=>0", "x_4=>1", "x_6=>1"}, {"x_6=>0", "x_4=>1", "x_5=>1"}})
///

end

restart
uninstallPackage"SymbolicPowers"
restart
installPackage"SymbolicPowers"
viewHelp"SymbolicPowers"

restart
loadPackage"SymbolicPowers"
R = QQ[x,y,z]
I = ideal"x,y,z"
symbolicPower(I,2)
check"SymbolicPowers"


-- branden
restart
n = 3
R = ZZ/101[x_1..x_n]
I = ideal(apply(1..n, l -> x_1*x_l) )
loadPackage"SymbolicPowers"
symbolicPower(I,2)
check "SymbolicPowers"

R=QQ[x,y,z]
I=ideal(x)
symbolicPower(2,I)
toString I
primaryDecomposition I

F = res(R^1/I)
c = codim(R^1/I) 
p = F.Resolution.length
rk = apply(p, l -> r_l = rank(F_l))
rko = select(rk,odd)
rke = select(rk,even)
rk


rj = sum_{i=j}^p (-1)^{i-j} rk_i
r := j -> (
    ind = apply(p-j, l-> j+l);
    sum apply(ind, l -> if odd(l-j) then -1*rank(F_l) else rank(F_l))
    )
apply((c+1)..(p-1), l -> (
	if 
	l = 3
	height 
	r l
	F.dd#l
	minors(r l, F.dd#l)
loadPackage"SymbolicPowers"
bigHeight(I)
	)
	r l)

?minors

