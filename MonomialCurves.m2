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
  Key => MonomialCurves,
  Headline => "A package for computing symbolic powers of ideals defining space monomial curves",
   
   PARA {
       "This package completes the package SymbolicPowers by adding functions for computing symbolic powers of space monomial curves."},
  
   SUBSECTION "Contributors", "The following people have generously
   contributed code or worked on our code at various Macaulay2
   workshops.",
     
     UL {
	 "Ben Drabkin",
	 "Alexandra Seceleanu",
	 "Branden Stone",
	},

   SUBSECTION "A Quick Introduction",
   UL {
    TO "Monomial Curves",
    },

}  




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



	  



-- tests



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
