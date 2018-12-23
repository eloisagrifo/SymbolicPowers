newPackage(
        "SymbolicPowers",
	Version => "1.0", 
	Date => "Dec 23, 2018",
	Authors => {
	    {Name => "Eloisa Grifo", Email => "grifo@umich.edu", HomePage => "http://people.virginia.edu/~er2eq/"}
	    },
	Headline => "Calculations involving symbolic powers of space monomial curves",
	DebuggingMode => true
        )


export {    
    -- Methods
    "symbolicContainmentMonomialCurve",
    "symbolicPowerMonomialCurve"
    }


needsPackage "SymbolicPowers";

-----------------------------------------------------------
-----------------------------------------------------------
--Space monomial curves
-----------------------------------------------------------
-----------------------------------------------------------
    
curveIdeal = method(TypicalValue => Ideal)
curveIdeal(List) := Ideal => L -> (
    d := #L; 
    x := getSymbol "T";
    R := QQ(monoid[x_1 .. x_d]); 
    S := QQ(monoid[x_0]); 
    t := (gens S)_0;
    f := map(S,R,apply(L,i->t^i)); 
    ker f
    )

curveIdeal(Ring,List) := Ideal => (k,L) -> (
    d := #L; 
    x := getSymbol "T";
    R := k(monoid[x_1 .. x_d]); 
    S := k(monoid[x_0]); 
    t := (gens S)_0;
    f := map(S,R,apply(L,i->t^i)); 
    ker f
    )
    
symbolicContainmentMonomialCurve = method(TypicalValue => Boolean);
symbolicContainmentMonomialCurve(List,ZZ,ZZ) := Boolean => (L,m,n) -> (
    I := curveIdeal(L);
    isSymbPowerContainedinPower(I,m,n)
    )

symbolicContainmentMonomialCurve(Ring,List,ZZ,ZZ) := Boolean => (k,L,m,n) -> (
    I := curveIdeal(k,L);
    isSymbPowerContainedinPower(I,m,n)
    )

symbolicPowerMonomialCurve = method(TypicalValue => Ideal);
symbolicPowerMonomialCurve(List,ZZ) := Ideal => (L,m) -> (
    I := curveIdeal(L); 
    symbolicPower(I,m)
    )

symbolicPowerMonomialCurve(Ring,List,ZZ) := Ideal => (k,L,m) -> (
    I := curveIdeal(k,L); 
    symbolicPower(I,m)
    )


-----------------------------------------------------------
-----------------------------------------------------------
--Documentation
-----------------------------------------------------------
-----------------------------------------------------------

beginDocumentation()

document { 
  Key => SymbolicPowers,
  Headline => "A package for computing symbolic powers of ideals TESTING",
   
   PARA {
       "This package gives the ability to compute symbolic powers, and related invariants,
       of ideals in a polynomial ring or a quotient of a polynomial ring. For example, 
       in the context of the default behavior, ", TO "symbolicPower", " assumes the 
       following definition of the symbolic power of an ideal ", TEX /// I ///, ",", 
       TEX /// $$I^{(n)} = \cap_{p \in Ass(R/I)}(I^nR_p \cap R ),$$ ///,
       "as defined by M. Hochster and C. Huneke."},

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
       {"Hailong Dao, Alessandro De Stefani, Eloísa Grifo, Craig Huneke, and Luis Núñez-Betancourt. ", 
	   EM "Symbolic powers of ideals", ", ", HREF("https://arxiv.org/abs/1708.03010","https://arxiv.org/abs/1708.03010")} 
       },
  
   SUBSECTION "Contributors", "The following people have generously
   contributed code or worked on our code at various Macaulay2
   workshops.",
     
     UL {
	 "Ben Drabkin",
	 "Andrew Conner",
	 "Alexandra Seceleanu",
	 "Branden Stone",
	 "Xuehua (Diana) Zhong"
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
	      
	      1. If $I$ is squarefree monomial ideal, intersects the powers of the associated primes of $I$;
	      
	      2. If $I$ is monomial ideal, but not squarefree, takes an irredundant primary decomposition of $I$ and intersects the powers of those ideals;
	      
	      3. If $I$ is a saturated homogeneous ideal in a polynomial ring whose height is one less than the dimension of the ring, returns the saturation of $I^n$;
	      	      
	      4. If all the associated primes of $I$ have the same height, computes a primary decomposition of $I^n$ and intersects the components with radical $I$;
	      
	      5. If all else fails, compares the radicals of a primary decomposition of $I^n$ with the associated primes of $I$, and intersects the components corresponding to minimal primes.
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
	      We can also test it a bit faster, without computing the symbolic powers of $P$.
	      
	 Example
	      isSymbolicEqualOrdinary(P,2)

///



doc ///
     Key
     	  "The Containment Problem"
     Description
     	 Text
	      Given an ideal $I$, we can determine if $I^{(m)} \subseteq I^n$. For example, here is an ideal that fails the containment $I^{(3)} \subseteq I^2$:
	      
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
	      For example, if $I$ is the ideal defining the monomial curve defined by $t^3, t^4, t^5$ over $\mathbb{Z}/101$, we can ask whether $I^{(3)} \subseteq I^2$:
	      
	 Example     
	      symbolicContainmentMonomialCurve(ZZ/101,{3,4,5},3,2)
	      
     	 Text
	      Or we simply ask for the symbolic powers of these ideals. For example, here is the third symbolic power of the same ideal:
	      
	 Example     
	      symbolicPowerMonomialCurve(ZZ/101,{3,4,5},3)
///



doc ///
     Key
     	  "The Packing Problem"
     Description
     	 Text
	      Given a square-free monomial ideal $I$ of codimension $c$, $I$ is Konig if it contains a regular sequence of monomials of length $c$.
     	 
	      We can test if a given ideal is Konig:
	      
	 Example     
	      R = QQ[x,y,z]
	      I = ideal(x*y,z*y,x*z)
	      isKonig(I)
	      
     	 Text
	      $I$ is said to have the packing property if any ideal obtained from $I$ by setting any number of variables equal to 0 is Konig.
	      
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
       computes the big height of an ideal
   Usage
       bigHeight(I)
   Inputs
        I:Ideal
   Outputs
       :ZZ
           the largest height of an associated prime of I
   Description
       Text  
       	   Big height of an ideal: the largest height of an associated prime. 
           The algorithm is based on the following result by Eisenbud-Huneke-Vasconcelos, 
	   in their 1993 Inventiones Mathematicae paper:
	   
	   $\bullet$ codim $Ext^d(M,R) \geq d$ for all $d$
	   
	   $\bullet$ If $P$ is an associated prime of $M$ of codimension $d :=$ codim $P > $ codim $M$, 
	   then codim $Ext^d(M,R) = d$ and the annihilator of $Ext^d(M,R)$ is contained in $P$
	   
	   $\bullet$ If codim $Ext^d(M,R) = d$, then there really is an associated prime of codimension $d$.

       Example
           R = QQ[x,y,z,a,b]
     	   J = intersect(ideal(x,y,z),ideal(a,b))
    	   bigHeight(J)
   SeeAlso
       codim
       assPrimesHeight
   Caveat
       bigHeight works faster than assPrimesHeight
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
	   
	   $\bullet$ codim $Ext^d(M,R) \geq d$ for all $d$
	   
	   $\bullet$ If $P$ is an associated prime of $M$ of codimension $d :=$ codim $P > $ codim $M$, 
	   then codim $Ext^d(M,R) = d$ and the annihilator of $Ext^d(M,R)$ is contained in $P$
	   
	   $\bullet$ If codim $Ext^d(M,R) = d$, then there really is an associated prime of codimension $d$.	   

       Example
           R = QQ[x,y,z,a,b]
     	   J = intersect(ideal(x,y,z),ideal(a,b))
    	   assPrimesHeight(J)
   SeeAlso
       bigHeight
       codim
   Caveat
       bigHeight works faster than using assPrimesHeight and then taking the maximum
///


doc ///
   Key
       isSymbPowerContainedinPower
       (isSymbPowerContainedinPower, Ideal, ZZ, ZZ)
   Headline
       tests if the m-th symbolic power an ideal is contained the n-th power
   Usage
       isSymbPowerContainedinPower(I,m,n)
   Inputs
        I:Ideal
    	m:ZZ
    	n:ZZ
   Outputs
       :Boolean
           whether the m-th symbolic power of $I$ is contained in the n-th power
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
       minimalPart
       (minimalPart, Ideal)
   Headline
       intersection of the minimal components
   Usage
       minimalPart(I)
   Inputs
        I:Ideal
   Outputs
       :Ideal
           the intersection of the components of I corresponding to minimal primes
   Description
       Text  
       	   Eliminates embedded components of a given ideal

       Example
           R = QQ[x,y,z]
     	   J = intersect(ideal(x^2,y,z^3),ideal(x,z))
    	   minimalPart(J)
   SeeAlso
       assPrimesHeight
       bigHeight
       symbolicPower
///




doc ///
   Key
       containmentProblem
       (containmentProblem, Ideal, ZZ)
   Headline
       computes the smallest symbolic power contained in a power of an ideal.
   Usage
       containmentProblem(I,n)
   Inputs
	I:Ideal
	n:ZZ
   Outputs
       :ZZ
           the minimum value m such that the m-th symbolic power of I is contained in I^n
   Description
       Text
       	   Given an ideal $I$ and an integer $n$, containementProblem returns the order of the smallest symbolic power of $I$ contained in $I^n$.

       Example
	   B = QQ[x,y,z];
	   f = map(QQ[t],B,{t^3,t^4,t^5})
	   I = ker f;
	   m = containmentProblem(I,2)
   SeeAlso
       isSymbPowerContainedinPower
///




doc ///
   Key
       symbPowerPrimePosChar
       (symbPowerPrimePosChar, Ideal, ZZ)
   Headline
       
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
           Given a prime ideal $I$ in a polynomial ring over a field of positive characteristic, and an integer $n$, 
	   this method returns the $n$-th symbolic power of $I$.  To compute $I^{(a)}$, find the largest value $k$ with 
	   $q = p^k \leq a$. Then $I^{(a)} = (I^{[q]} : I^{a-q+1})$.

       Example 
           B = ZZ/7[x,y,z];
	   f = map(ZZ/7[t],B,{t^3,t^4,t^5})
	   I = ker f;
	   symbPowerPrimePosChar(I,2)
   Caveat
       The ideal must be prime.
   SeeAlso
       symbolicPower
///



doc ///
   Key
       symbolicPower
       (symbolicPower, Ideal, ZZ)
   Headline
       computes the symbolic power of an ideal.
   Usage
       	symbolicPower(I,n)
   Inputs
        I:Ideal
	n:ZZ
   Outputs
       :Ideal
           the n-th symbolic power of I
   Description
       Text
              Given an ideal $I$ and an integer $n$, this method returns the $n$-th symbolic power of $I$. Various algorithms are used, in the following order:     
	      
	      1. If $I$ is squarefree monomial ideal, intersects the powers of the associated primes of $I$;
	      
	      2. If $I$ is monomial ideal, but not squarefree, takes an irredundant primary decomposition of $I$ and intersects the powers of those ideals;
	      
	      3. If $I$ is a saturated homogeneous ideal in a polynomial ring whose height is one less than the dimension of the ring, returns the saturation of $I^n$;
	      
	      4. If $I$ is an ideal with only degree one primary components, intersects the powers of the primary components of I.
	      
	      5. If all the associated primes of $I$ have the same height, computes a primary decomposition of $I^n$ and intersects the components with radical $I$;
	      
	      6. If all else fails, compares the radicals oyf a primary decomposition of $I^n$ with the associated primes of $I$, and intersects the components corresponding to minimal primes.
 
       Example
              B = QQ[x,y,z];
	      f = map(QQ[t],B,{t^3,t^4,t^5})
	      I = ker f;
	      symbolicPower(I,2)
	      
       Text
       	   When computing symbolic powers of a quasi-homogeneous ideal, the method runs faster if the ideal is changed to be homegeneous.
	   
       Example
       	   P = ker map(QQ[t],QQ[x,y,z],{t^3,t^4,t^5})
	   isHomogeneous P
	   time symbolicPower(P,4);
	   Q = ker map(QQ[t],QQ[x,y,z, Degrees => {3,4,5}],{t^3,t^4,t^5})
	   isHomogeneous Q
	   time symbolicPower(Q,4);

   SeeAlso
      symbPowerPrimePosChar
///



doc ///
   Key
       isSymbolicEqualOrdinary
       (isSymbolicEqualOrdinary, Ideal, ZZ)
   Headline
    	tests if symbolic power is equal to ordinary power       
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
           Given a radical ideal I and an integer $n$, this method returns true if and only if $I^n=I^{(n)}$. 
	   This method circumvents computing the symbolic powers in most cases, by first testing the @TO bigHeight@ of $I^n$

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
       	   the join of I and J
   Description
       Text    
           This method uses Seth Sullivant's results found in "Combinatorial symbolic powers", J. Algebra 319 (2008), no. 1, 115-142.

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
         computes the symbolic power of the prime ideal using join of ideals.
     Usage 
         symbolicPowerJoin(P,n)
     Inputs 
	  P:Ideal
	  n:ZZ
     Outputs
          :Ideal
	      the n-th symbolic power of P
     Description	  
       Text
	   Computes the $n$-th symbolic power of the prime ideal $P$, using join of ideals.
	   
	   This is the algorithm in Seth Sullivant's "Combinatorial symbolic powers", J. Algebra 319 (2008), no. 1, 115-142.

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
         tests the containment of symbolic in ordinary powers of ideals for monomial curves.
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
	   Tests whether $I^{(m)} \subseteq I^n$, where $I$ is the defining ideal for the monomial curve defined by $t^{a_1}, \ldots, t^{a_n}$. 
	   If no field is provided, the ideal is defined over $\mathbb{Q}$.

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
         computes the symbolic powers of ideals defining monomial curves.
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
	   Finds the $m$-th symbolic power of $I$, where $I$ is the defining ideal for the monomial curve defined 
	   by $t^{a_1}, \ldots, t^{a_n}$. If no field is provided, the ideal is defined over $\mathbb{Q}$.

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
         returns all square-free monomials in a minimal generating set of the given ideal.
     Usage 
         squarefreeGens(I)
     Inputs 
     	  I:Ideal
     Outputs
          :List
     Description	  
       Text
	   Given a monomial ideal $I$, returns all square-free monomials in a minimal generating set of $I$.

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
         finds square-fee monomials in ideal raised to the power of the codimension.
     Usage 
         squarefreeInCodim(I)
     Inputs 
     	  I:Ideal
     Outputs
          :List
     Description	  
       Text
	   Given a monomial ideal $I$, returns all square-free monomials in a minimal generating set of $I^c$ where $c$ is the codimension of $I$.

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
         determines if a given square-free ideal is Konig.
     Usage 
         isKonig(I)
     Inputs 
     	  I:Ideal
     Outputs
          :Boolean
     Description	  
       Text
	   Given a square-free monomial ideal $I$, determines if the ideal is Konig. 
	   A square-free monomial ideal $I$ of codimension $c$ is Konig if it contains a regular sequence of monomials of length $c$.

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
         determines if a given square-free ideal is packed.
     Usage 
         isPacked(I)
     Inputs 
     	  I:Ideal
     Outputs
          :Boolean
     Description	  
       Text
	   Given a square-free monomial ideal $I$, determines if the ideal is Konig.
	   A square-free monomial ideal $I$ of codimension $c$ is packed if every ideal obtained from it by replacing any number of variables by 1 or 0 is Konig.

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
         finds a substitution of variables by 1 and/or 0 for which an ideal is not Konig.
     Usage 
         noPackedSub(I)
     Inputs 
     	  I:Ideal
     Outputs
          :List
     Description	  
       Text
	   Given an ideal that is not packed, returns a substitution of variables by 0 and/or 1 that produces an ideal that is not Konig.
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
         finds all substitutions of variables by 1 and/or 0 for which ideal is not Konig.
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
         returns the minimal degree of a given symbolic power of an ideal.
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
	 (lowerBoundResurgence,Ideal)
     Headline 
         computes a lower bound for the resurgence of a given ideal.
     Description
       Text
           The resurgence of an ideal $I$, defined by Harbourne and Bocci, is given by
	 $\rho(I) :=$ sup $\lbrace a/b : I^{(a)}$ &nsub; $I^b \rbrace.$
     Usage 
         lowerBoundResurgence(Ideal)
     Inputs 
     	  I:Ideal
     Outputs
          :QQ
     Description	  
       Text
	   Given an ideal $I$, finds the maximum of the quotients $m/k$ that fail $I^{(m)} \subseteq I^k$ with $k \leq$ the optional input SampleSize.

       Example 
	   T = QQ[x,y,z];
	   I = intersect(ideal"x,y",ideal"x,z",ideal"y,z");
	   lowerBoundResurgence(I)

///

doc ///
     Key 
         UseWaldschmidt
     Headline 
         optional input for computing a lower bound for the resurgence of a given ideal.
     Usage 
         lowerBoundResurgence(Ideal,UseWaldschmidt=>true)
     Inputs 
     	  I:Ideal
     Outputs
          :QQ
     Description	  
       Text
	   Given an ideal $I$ and an integer $n$, returns the larger value between the 
	   maximum of the quotients $m/k$ that fail $I^{(m)} \subseteq I^k$ with $k \leq n$ 
	   and $\frac{\alpha(I)}{waldschmidt(I)}$. 

       Example 
	   T = QQ[x,y,z];
	   I = intersect(ideal"x,y",ideal"x,z",ideal"y,z");
	   lowerBoundResurgence(I,UseWaldschmidt=>true)

///


doc ///
     Key 
         [lowerBoundResurgence,SampleSize]
     Headline 
         optional parameter used for approximating asymptotic invariants that are defined as limits.
     Usage 
         lowerBoundResurgence(I,SampleSize=>ZZ)
     Description	  
         Text
       	   Given an ideal $I$ and an integer $n$, returns the larger of the two numbers $\frac{\alpha(I)}{waldschmidt(I)}$ 
	   and the maximum of the quotients $m/k$ that fail $I^{(m)} \subseteq I^k$ with $k \leq$ @TO SampleSize@.
     
         Example
           R = QQ[x,y,z];
	   J = ideal (x*(y^3-z^3),y*(z^3-x^3),z*(x^3-y^3));
	   lowerBoundResurgence(J, SampleSize=>5)
///


doc ///
     Key 
         [lowerBoundResurgence,UseWaldschmidt]
     Headline 
         optional input for computing a lower bound for the resurgence of a given ideal.
     Usage 
         lowerBoundResurgence(Ideal,UseWaldschmidt=>true)
     Inputs 
     	  I:Ideal
     Outputs
          :QQ
     Description	  
       Text
	   Given an ideal $I$ and an integer $n$, returns the larger value between the 
	   maximum of the quotients $m/k$ that fail $I^{(m)} \subseteq I^k$ with $k \leq$ @TO SampleSize@ 
	   and $\frac{\alpha(I)}{waldschmidt(I)}$. 

       Example 
	   T = QQ[x,y,z];
	   I = intersect(ideal"x,y",ideal"x,z",ideal"y,z");
	   lowerBoundResurgence(I,UseWaldschmidt=>true)

///



doc ///
     Key 
         symbolicPolyhedron
	 (symbolicPolyhedron,Ideal)
	 (symbolicPolyhedron,MonomialIdeal)
     Headline 
         computes the symbolic polyhedron for a monomial ideal. 
     Usage 
         symbolicPolyhedron(I)
     Inputs 
     	  I:Ideal
     Outputs
          :Polyhedron 
     Description	  
       Text
	   The symbolic polyhedron associated to a monomial ideal $I$ is defined in the paper "Symbolic Powers of Monomial Ideals" 
	   by S. M. Cooper, R. J. D. Embree, H. T. Ha, A. H. Hoefel. The symbolic polyhedron contains the exponent vector of any
	   monomial in $I^n$ scaled by $1/n$.
	  
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
         computes the Waldschmidt constant for a homogeneous ideal. 
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
	   over a finite number of exponents $n$, namely for $n$ from 1 to the optional parameter @TO SampleSize@.  
       
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
         optional parameter used for approximating asymptotic invariants that are defined as limits.
     SeeAlso
     	 waldschmidt
	 lowerBoundResurgence
	 asymptoticRegularity    
///	   

doc ///
     Key 
         [waldschmidt,SampleSize]
     Headline 
         optional parameter used for approximating asymptotic invariants that are defined as limits.
     Usage 
         waldschmidt(I,SampleSize=>ZZ)
     Description	  
         Text
       	   For ideals that are not monomial, we give an approximation of the Waldschmidt constant by taking the minimum value of $\frac{\alpha(I^{(n)})}{n}$
	   over a finite number of exponents $n$, namely for $n$ from 1 to the optional parameter @TO SampleSize@. Similarly the @TO SampleSize@ is used to give an
	   approximation for the asymptotic regularity by computing the smallest value of $\frac{reg(I^{(n)})}{n}$ for $n$ from
	   1 to the @TO SampleSize@.
     
         Example
           R = QQ[x,y,z];
	   J = ideal (x*(y^3-z^3),y*(z^3-x^3),z*(x^3-y^3));
	   waldschmidt(J, SampleSize=>5)
///	   

doc ///
     Key 
         [asymptoticRegularity,SampleSize]
     Headline 
         optional parameter used for approximating asymptotic invariants that are defined as limits.
     Usage 
         asymptoticRegularity(I,SampleSize=>ZZ)
     Description	  
         Text
       	   We give an approximation of the asymptotic regularity by taking the minimum value of $\frac{reg(I^{(n)})}{n}$
	   over a finite number of exponents $n$, namely for $n$ from 1 to the optional parameter @TO SampleSize@;
	   the default value for @TO SampleSize@ is 10. 
     
         Example
           R = QQ[x,y,z];
	   J = ideal (x*(y^3-z^3),y*(z^3-x^3),z*(x^3-y^3));
	   asymptoticRegularity(J, SampleSize=>5)
///	   


doc ///
     Key 
         InSymbolic
     Headline 
         an optional parameter used in containmentProblem.
     SeeAlso
     	 containmentProblem

///	   

doc ///
     Key 
       	 [containmentProblem,InSymbolic]
     Headline 
         an optional parameter used in containmentProblem.
     Usage 
         containmentProblem(I,n,InSymbolic => true)
     Description	  
         Text
       	   Given an ideal I and an integer n, @TO InSymbolic@ is used to ask the following question:
	   What is the largest power containing the symbolic power $I^{(n)}$?

         Example
           R = QQ[x,y,z];
	   J = ideal (x*(y^3-z^3),y*(z^3-x^3),z*(x^3-y^3));
	   containmentProblem(J,3,InSymbolic => true)
///	   
	   
doc ///
     Key 
         asymptoticRegularity
	 (asymptoticRegularity,Ideal)
     Headline 
         approximates the asymptotic regularity 
     Usage 
         asymptoticRegularity(I,SampleSize=>ZZ)
     Description
         Text	  
       	   We give an approximation of the asymptotic regularity by taking the minimum value of $\frac{reg(I^{(n)})}{n}$
	   over a finite number of exponents $n$, namely for $n$ from 1 to the optional parameter @TO SampleSize@;
	    the default value for @TO SampleSize@ is 10. 
     
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
    	computes the symbolic defect of an ideal
   Usage
         symbolicDefect(I,m)
   Inputs
         I:Ideal
         m:ZZ
   Outputs
          :ZZ
             the size of a minimal generating set of the m-th symbolic power of I modulo I^m.
   Description
       Text
       	   Given an ideal $I$ and integer $m$, this method returns the size of a minimal generating set for the $m$-th symbolic power of $I$ modulo $I^m$.

       Example
         R = QQ[x,y,z]    
         I = ideal(x*y,x*z,y*z);					      
	 symbolicDefect(I,2)
 ///

doc ///
    Key
    	UseMinimalPrimes
    	[symbolicPower,UseMinimalPrimes]
    	[isSymbPowerContainedinPower,UseMinimalPrimes]
    	[symbolicDefect,UseMinimalPrimes]	
    	[containmentProblem,UseMinimalPrimes]
    Headline	 
    	an option to only use minimal primes to calculate symbolic powers
    Description
    	Text
	    The default value is false. When defined to be true, the symbolic power is calculated as defined in Villarreal. 
	    In particular, @TO symbolicPower@ has the option to restrict to minimal primes 
	    versus use all associated primes with @TO UseMinimalPrimes@. With this option the
	    symbolic power of an ideal $I$ is defined as 
	    $$I^{(n)} = \cap_{p \in Min(R/I)}(I^nR_p \cap R ),$$
	    where $Min(R/I)$, is the set of minimal primes in $I$.
	    
       Text
       	   R. Villarreal. "Monomial algebras" Second edition. Monographs and Research Notes in Mathematics. CRC Press, Boca Raton, FL, 2015. xviii+686 pp. ISBN: 978-1-4822-3469-5.

    SeeAlso
    	containmentProblem
	isSymbPowerContainedinPower
	symbolicDefect	  
	symbolicPower
///

doc /// 
    Key
    	CIPrimes
	[symbolicPower,CIPrimes]
	[isSymbPowerContainedinPower,CIPrimes]
	[symbolicDefect,CIPrimes]
	[containmentProblem,CIPrimes]
    Headline
    	an option to compute the symbolic power by taking the intersection of the powers of the primary components
    Description
    	Text
	    The default value is false.  When defined to be true, the @TO symbolicPower@ function tests whether the primary components are complete intersections having the same height.  If each component is, then the function takes the intersection of the powers of the components:
	     $$I^{(n)}=\cap_{p\in Ass(R/I)} p^n.$$
    SeeAlso
    	containmentProblem
	isSymbPowerContainedinPower
	symbolicDefect
	symbolicPower
///



{* Defunct since we change the order of the monomial tests. The symbolic powers method first considers
   Monomial Ideals so there is no need for a monomial option. 
doc ///
    Key
    	UseMonomial
    	[symbolicPower,UseMonomial]
    Headline	 
    	an option to only use monomial ideal methods to calculate symbolic powers
    Description
    	Text
	    The default value is false. When defined to be true, the symbolic power is calculated 
	    methods particular to monomial ideals. If $I$ is square-free, the symbolic powers 
	    of $I$ are obtained by intersecting the powers of its associated primes. If $I$ is 
	    simply monomial, one can collect the primary components in a decomposition
	    of $I$ and intersect the powers of the maximal ones. 
	    
	    The ideal $I$ must be defined using @TO monomialIdeal@. 
	    
	Example
	    R = ZZ/101[x,y,z]
	    I = monomialIdeal(x*y,x*z,y*z)
	    symbolicPower(I,5, UseMonomial => true)	   
	   
    SeeAlso
	symbolicPower
///
*}

-- tests

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

TEST ///
R=QQ[x,y,z]
I=ideal(x*(y^5-z^5),y*(z^5-x^5),z*(x^5-y^5))
assert(symbolicPower(I,3,CIPrimes => true)==symbolicPower(I,3))
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
--TEST ///
--R=ZZ/3[x,y]
--I=ideal(x*y^2+1,x^2)
--assert(frobeniusPower(I,9)==ideal(x^9*y^(19)+1,x^(18)))
--///

--lowerBoundResurgence
TEST ///
R=QQ[x,y,z]
I=ideal(x*y,x*z,y*z)
assert(lowerBoundResurgence(I)==6/5)
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
 needsPackage"Polyhedra"
 R = QQ[x,y,z];
 I = ideal(x*y,y*z,x*z);
 assert((vertices symbolicPolyhedron I)== matrix{{1,1,0,1/2},{1,0,1,1/2},{0,1,1,1/2}})
///

-- waldschmidt
TEST ///
 R = QQ[x,y,z];
 I = ideal(x*y,y*z,x*z);
 assert(waldschmidt(I)==3/2)
///

TEST ///
R=QQ[x,y,z,Degrees=>{9,11,13}];
S=QQ[t]
I=kernel(map(S,R,{t^9,t^11,t^13}))
J=ideal(apply(flatten entries gens gb I,leadTerm))
assert(waldschmidt(I)==22)
assert(waldschmidt(J)==22)
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
loadPackage"SymbolicPowers"

restart
uninstallPackage"SymbolicPowers"
restart
installPackage"SymbolicPowers"
viewHelp"SymbolicPowers"
check"SymbolicPowers"

needsPackage"SymbolicPowers"
R = QQ[x,y]
I = ideal"x+y"
symbolicPolyhedron I

restart
-- Paper Example Ideal of height dim R-1
loadPackage "SymbolicPowers";
R=QQ[x,y,z];
I=ideal(x*(y^3-z^3),y*(z^3-x^3),z*(x^3-y^3));
symbolicPower(I,3);
symbolicPower(I,3)==saturate(I^3)

-- Paper Example Primary ideals
restart
loadPackage "SymbolicPowers";
R=QQ[w,x,y,z]/(x*y-z^2);
I=ideal(x,z);
symbolicPower(I,2)

restart
-- Paper Example Monomial Ideal
loadPackage "SymbolicPowers";
R = QQ[x,y,z];
I = ideal(x*y,x*z,y*z)
symbolicPower(I,2)

restart
-- Paper Example Containment Problem
loadPackage "SymbolicPowers";
R=QQ[x,y,z];
I=ideal(x*(y^3-z^3),y*(z^3-x^3),z*(x^3-y^3));
containmentProblem(I,2)

restart
-- Paper Example Waldschmidt constants of monomial ideals
loadPackage "SymbolicPowers";
R=QQ[x,y,z];
I=ideal(x*y,x*z,y*z);
symbolicPolyhedron(I)
waldschmidt I

restart
-- Paper Example Waldschmidt constants of arbitrary ideals
loadPackage "SymbolicPowers";
R=QQ[x,y,z];
I=ideal(x*(y^3-z^3),y*(z^3-x^3),z*(x^3-y^3));
waldschmidt I


lowerBoundResurgence(I)



------testing CIPRimes
loadPackage "SymbolicPowers"
loadPackage "Points"
I=randomPoints(2,10);
time symbolicPower(I,6,CIPrimes=>true);
time symbolicPower(I,6);
