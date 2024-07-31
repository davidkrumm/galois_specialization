/* 
This file contains MAGMA code used for constructing dynamical modular curves.
This includes:
 - Auxiliary functions (starting on line 13)
 - Construction of the curve Z_f for a rational function f (line 106)
 - Construction of dynatomic polynomials and curves (line 130)
 - Construction of generalized dynatomic polynomials and curves (line 168)
 - Construction of trace polynomials and curves (line 200)
 - Construction of preimage curves (line 240)
 - Construction of standard maps between modular curves (line 262)
 */
 
// Returns the n-fold composition of the rational function phi with itself.
Iterate := function(phi,n)
	assert n ge 0;
	z := Parent(phi).1;
	if n eq 0 then
		return z;
	end if;
	phi_n := z;
	for i := 1 to n do
		phi_n := Evaluate(phi_n,phi);
	end for;
	return phi_n;
end function;
 
/* Given a nonconstant rational function p(t1,...tn,x) in Q(t1,...,tn)(x),
and a sequence of variables (a1,...,an,b), returns p(a1,...,an,b). */
Substitute := function(p, vars)
N := #vars;
assert N ge 2;
first_vars := Remove(vars,N);
if N gt 2 then
	value_num := Evaluate(Polynomial([Evaluate(c, first_vars) : c in Coefficients(Numerator(p))]), vars[N]);
	value_den := Evaluate(Polynomial([Evaluate(c, first_vars) : c in Coefficients(Denominator(p))]), vars[N]);
else
	value_num := Evaluate(Polynomial([Evaluate(c, vars[1]) : c in Coefficients(Numerator(p))]), vars[N]);
	value_den := Evaluate(Polynomial([Evaluate(c, vars[1]) : c in Coefficients(Denominator(p))]), vars[N]);
end if;
return value_num/value_den;
end function;
 
/* Given a nonzero rational function p in one variable with rational coefficients,
returns the union of the sets of rational zeros and rational poles of p. */
ZerosAndPoles := function(p)
	p_degree :=  Max(Degree(Numerator(p)),Degree(Denominator(p)));
	if p_degree eq 0 then
		return {};
	else
		return {r[1]: r in Roots(Numerator(p))} join {r[1]: r in Roots(Denominator(p))};
	end if;
end function;

/* Given a nonconstant rational function f with coefficients in a function field over Q,
returns p, A, B, where p is the content of f and A, B are coprime and primitive polynomials
with coefficients in a polynomial ring over Q such that f = p*A/B.
If the coefficients of f lie in a one-variable function field, the exceptional set
of f over Q is also returned. */
Normalize := function(f)
	// Ensure that f has coefficients in a function field.
	Qt := FieldOfFractions(CoefficientRing(Parent(f)));
	a := Numerator(f);
	b := Denominator(f);
	a := Polynomial([Qt ! coeff : coeff in Coefficients(a)]);
	b := Polynomial([Qt ! coeff : coeff in Coefficients(b)]); 
	f_copy := a/b;
	// Now a,b, and f_copy have coefficients in a function field.
	
	// Find the content and primitive part of a and b.
	a_lcm := LCM([Denominator(coeff): coeff in Coefficients(a)]);
	a_gcd := GCD([Numerator(coeff): coeff in Coefficients(a*a_lcm)]);
	a_content := a_gcd/a_lcm;
	b_lcm := LCM([Denominator(coeff): coeff in Coefficients(b)]);
	b_gcd := GCD([Numerator(coeff): coeff in Coefficients(b*b_lcm)]);
	b_content := b_gcd/b_lcm;
	
	// Verify we have found the content of f, and A, B as required.
	f_content := a_content/b_content;
	A := a/a_content;
	B := b/b_content;
	assert f_copy eq f_content*A/B;
	// Check that that A, B have coefficients in a polynomial ring.
	assert {Denominator(coeff) : coeff in Coefficients(A)} eq {1};
	assert {Denominator(coeff) : coeff in Coefficients(B)} eq {1};
	// Create A, B as polynomials with coefficients in a polynomial ring.
	A := Polynomial([Numerator(coeff) : coeff in Coefficients(A)]);
	B := Polynomial([Numerator(coeff) : coeff in Coefficients(B)]);
	// Check that A,B are coprime and primitive.
	assert GCD(A,B) eq 1;
	assert Content(A) eq 1 and Content(B) eq 1;
	
	if 	Rank(Qt) gt 1 then
		return f_content, A, B;
	else
		// Construct the exceptional set of f.
		AA := AffineSpace(Rationals(),2);
		A_sub := Substitute(A,[AA.1,AA.2]);
		B_sub := Substitute(B,[AA.1,AA.2]);
		X := Scheme(AA,[A_sub,B_sub]);
		assert Dimension(X) in {0,-1};
		exceptional_set := ZerosAndPoles(f_content) join {p[1]: p in RationalPoints(X)};
		return f_content, A, B, exceptional_set;
	end if;
end function;

/* Given a nonconstant rational function f with coefficients in a function field over Q,
returns the list of irreducible components of the curve Z_f,
as well as the intersection of Q with the exceptional set of f. */
Z := function(f)
	_, A, _, exc := Normalize(f);
	assert Degree(A) ne 0;
	// Construct the irreducible components of the curve A(t,x) = 0.
	AA := AffineSpace(Rationals(),2);
	A_sub := Substitute(A,[AA.1,AA.2]);
	A_curves := [Curve(AA,fac[1]): fac in Factorization(A_sub)];
	return A_curves, exc;
end function;

/* Given a nonconstant rational function phi with coefficients in a function field over Q,
returns the intersection of Q with the bad set of phi.*/
BadSet := function(phi)
p, A, B,_ := Normalize(phi);
A_roots := {r[1]: r in Roots(LeadingCoefficient(A))};
B_roots := {r[1]: r in Roots(LeadingCoefficient(B))};
Res_roots := {r[1]: r in Roots(Resultant(A,B))};
return ZerosAndPoles(p) join A_roots join B_roots join Res_roots;
end function;


/// *** Construction of dynatomic polynomials and curves. *** ///

/* Computes a normalized nth dynatomic polynomial of f,
as well as the content of the nth dynatomic polynomial.
If A is the normalization and p is the content, we have Phi_n = p*A. */
DynatomicPolynomial := function(phi,n)
	assert n ge 1;
	F := FieldOfFractions(Parent(phi));
	z := F.1;
	PHI := F ! 1;
	phi_iterate := z;
	for k := 1 to n do
		phi_iterate := Evaluate(phi_iterate, phi);
		if n mod k eq 0 then
			p := Numerator(phi_iterate);
			q := Denominator(phi_iterate);
			PHI *:= (z*q - p)^MoebiusMu(n div k);
		end if;
	end for;
	assert Denominator(PHI) eq 1;
	PHI := Numerator(PHI);
	p, A, B := Normalize(PHI); // PHI = p*A/B
	assert B eq 1;
	return A, p;
end function;

/* Computes an affine plane model of the nth dynatomic curve Y_1(n) for a given map phi.
A list of irreducible components of Y_1(n) is returned.
In addition, a finite subset F of Q is returned, with the property that if
c is not in F and alpha is an n-periodic point of phi_c, then the pair (c,alpha)
represents a point on Y_1(n). */
DynatomicCurves := function(phi,n)
	PHI, p := DynatomicPolynomial(phi,n);
	curves, exc := Z(PHI);
	return curves, BadSet(phi) join exc join ZerosAndPoles(p);
end function;


/// *** Construction of generalized dynatomic polynomials and curves. *** ///

/* Computes a normalized generalized dynatomic polynomial of phi,
as well as the content of the generalized dynatomic polynomial.
If A is the normalization and p is the content, we have Phi_{m,n} = p*A. */
GeneralizedDynatomicPolynomial := function(phi,m,n)
	assert m ge 1 and n ge 1;
	Phi_n, Phi_n_content := DynatomicPolynomial(phi,n);
	fm1 := Iterate(phi,m - 1);
	fm := Evaluate(fm1,phi);
	PHI := Evaluate(Phi_n,fm)/Evaluate(Phi_n,fm1);
	D := Degree(Phi_n);
	PHI *:= Denominator(fm)^D/Denominator(fm1)^D;
//	f_degree := Max(Degree(Numerator(f)),Degree(Denominator(f)));
//	S := &+[f_degree^d*MoebiusMu(n div d) : d in Divisors(n)];
//	PHI *:= Denominator(fm)^S/Denominator(fm1)^S;
	p, A, B := Normalize(PHI); // PHI = p*A/B
	assert B eq 1;
	return A, p;
end function;

/* Computes an affine plane model of the generalized dynatomic curve Y_1(m,n).
A list of irreducible components of Y_1(m,n) is returned.
In addition, a finite subset F of Q is returned, with the property that if
c is not in F and alpha is a point of pre-periodic type (m,n) for phi_c, 
then the pair (c,alpha) represents a point on Y_1(m,n). */
GeneralizedDynatomicCurves := function(phi,m,n)
PHI, p := GeneralizedDynatomicPolynomial(phi,m,n);
curves, exc := Z(PHI);
return curves, BadSet(phi) join exc join ZerosAndPoles(p);
end function;

/// *** Construction of trace polynomials and curves *** ///

/* Computes a normalized nth trace polynomial of phi, as well as
the content of the trace polynomial. If A is the normalization
and p is the content, we have T_{n,phi} = p*A. */
TracePolynomial := function(phi,n)
	assert n ge 1;
	PHI, p := DynatomicPolynomial(phi,n); // Phi_n = p*PHI
	Qt := FieldOfFractions(CoefficientRing(Parent(PHI)));
	PHI := p*Polynomial([Qt ! coeff : coeff in Coefficients(PHI)]);
	lc := LeadingCoefficient(PHI);
	R := Parent(PHI); 
	z := R.1;
	trace := z;
	iterate := z;
	for i in [1..n-1] do
		iterate := Evaluate(phi,iterate);
		trace +:= iterate;
	end for;
	q := Numerator(trace);
	h := Denominator(trace);
	e := Maximum(Degree(h),Degree(q)) - Degree(h);
	_<y> := PolynomialRing(R);
	PHIy := Evaluate(PHI,y);
	hy := Evaluate(h,y);
	qy := Evaluate(q,y);
	quo := Resultant(PHIy,hy*z - qy)/(Resultant(PHI,h)*lc^e);
	_,trace_poly := IsPower(quo,n);
	assert Denominator(trace_poly) eq 1;
	content, A, B := Normalize(trace_poly);
	assert B eq 1;
	return A, content;
end function;

/* Computes an affine plane model of the nth trace curve Y_t(n).
A list of irreducible components of Y_t(n) is returned. */
TraceCurves := function(phi,n)
	return Z(TracePolynomial(phi,n));
end function;

/// *** Construction of preimage curves *** ///

/* Computes an affine plane model of the mth preimage curve Y(m,P), where P is a rational function.
A list of irreducible components of Y(m,P) is returned. In addition, a finite subset F of Q
is returned, with the property that if c is not in F and alpha is an algebraic number with
phi_c^m(alpha) = P(c), then the pair (c,alpha) represents a point on Y_1(m,P).*/
PreimageCurves_finite := function(phi,m,P)
	phi_m := Iterate(phi,m);
	curves, exc := Z(phi_m - P);
	return curves, BadSet(phi) join exc join {r[1] : r in Roots(Denominator(P))};
end function;

/* Computes an affine plane model of the mth preimage curve Y(m,infinity).
A list of irreducible components of Y(m,infinity) is returned. In addition, a finite subset
F of Q is returned, with the property that if c is not in F and alpha is an algebraic number with
phi_c^m(alpha) = infinity, then the pair (c,alpha) represents a point on Y(m,infinity). */
PreimageCurves_infinity := function(phi,m)
	phi_m := Iterate(phi,m);
	curves, exc := Z(1/phi_m);
	return curves, BadSet(phi) join exc;
end function;

/// *** Construction of standard maps between modular curves *** ///

// The map Y_1(n) -> Y_1(n) of order n
DynatomicAutomorphism := function(phi,n);
	AA := AffineSpace(Rationals(),2);
	PHI := DynatomicPolynomial(phi,n);
	g := Substitute(PHI,[AA.1,AA.2]);
	assert Denominator(g) eq 1;
	Y1_n := Curve(AA,Numerator(g));
	return map<Y1_n->Y1_n|[AA.1,Substitute(phi,[AA.1,AA.2])]>;
end function;

// The map Y_1(m,n) -> Y_1(i,n) for 1<= i < m
GeneralizedDynatomicMorphism := function(phi,m,n,i)
	assert i lt m and i ge 1;
	AA := AffineSpace(Rationals(),2);
	PHI := GeneralizedDynatomicPolynomial(phi,m,n);
	g := Substitute(PHI,[AA.1,AA.2]);
	assert Denominator(g) eq 1;
	Y1_mn := Curve(AA,Numerator(g));
	PHI := GeneralizedDynatomicPolynomial(phi,i,n);
	g := Substitute(PHI,[AA.1,AA.2]);
	assert Denominator(g) eq 1;
	Y1_in := Curve(AA,Numerator(g));
	iterate := Iterate(phi,m - i);
	return map<Y1_mn->Y1_in|[AA.1,Substitute(iterate,[AA.1,AA.2])]>;
end function;

// The map Y_1(n) -> Y_t(n)
TraceCovering := function(phi,n);
	AA := AffineSpace(Rationals(),2);
	PHI := DynatomicPolynomial(phi,n);
	g := Substitute(PHI,[AA.1,AA.2]);
	assert Denominator(g) eq 1;
	Y1_n := Curve(AA,Numerator(g));
	T := TracePolynomial(phi,n);
	g := Substitute(T,[AA.1,AA.2]);
	assert Denominator(g) eq 1;
	Yt_n := Curve(AA,Numerator(g));
	trace := &+[Iterate(phi,i) : i in [0..n-1]];
	return map<Y1_n->Yt_n|[AA.1,Substitute(trace,[AA.1,AA.2])]>;
end function;

// The map Y(m,P) -> Y(i,P) for 1 <= i <= m and P finite
PreimageMorphism_finite := function(phi,m,P,i)
	assert i ge 1 and i le m;
	// Ensure phi has coefficients in a one-variable function field.
	Qt := FieldOfFractions(CoefficientRing(Parent(phi)));
	a := Numerator(phi);
	b := Denominator(phi);
	a := Polynomial([Qt ! coeff : coeff in Coefficients(a)]);
	b := Polynomial([Qt ! coeff : coeff in Coefficients(b)]);
	phi_copy := a/b;
	// Construct the curve Y(m,P).
	_,A,_,_ := Normalize(Iterate(phi_copy,m) - (Qt ! P));
	AA := AffineSpace(Rationals(),2);
	g := Substitute(A,[AA.1,AA.2]);
	YmP := Curve(AA,g);
	// Construct the curve Y(i,P).	
	_,A,_,_ := Normalize(Iterate(phi_copy,i) - (Qt ! P));
	g := Substitute(A,[AA.1,AA.2]);
	YiP := Curve(AA,g);
	// Construct the map Y(m,P) -> Y(i,P).
	iterate := Iterate(phi,m - i);
	return map<YmP->YiP|[AA.1,Substitute(iterate,[AA.1,AA.2])]>;
end function;

// The map Y(m,infty) -> Y(i,infty) for 1 <= i <= m
PreimageMorphism_infinity := function(phi,m,i)
	assert i ge 1 and i le m;
	AA := AffineSpace(Rationals(),2);
	// Construct the curve Y(m,infty).
	_,A,_,_ := Normalize(1/Iterate(phi,m));
	g := Substitute(A,[AA.1,AA.2]);
	assert Degree(g) gt 0;
	YmP := Curve(AA,g);
	// Construct the curve Y(i,infty).	
	_,A,_,_ := Normalize(1/Iterate(phi,i));
	g := Substitute(A,[AA.1,AA.2]);
	assert Degree(g) gt 0;
	YiP := Curve(AA,g);
	// Construct the map Y(m,infty) -> Y(i,infty).
	iterate := Iterate(phi,m - i);
	return map<YmP->YiP|[AA.1,Substitute(iterate,[AA.1,AA.2])]>;
end function;
