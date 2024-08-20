load "Coleman/coleman.m";

SmallHeightRationals := function(bound)
	bounded_rationals := [* -1,0,1 *];
	B := Floor(bound);
	for den in [2 .. B] do
		for num in [1 .. den] do
			if Gcd(num,den) eq 1 then
				r := num/den;
				bounded_rationals cat:= [* r, -r, 1/r, -1/r *];
			end if;
		end for;
	end for;
	return bounded_rationals;
end function;

CurveSearch := function(curve,bound)
Y := curve;
Y_pts := {@ p : p in PointSearch(Y,bound) @};
A1 := AffineSpace(Rationals(),1);
Y_to_A1_1 := map<Y->A1 | [Y.1]>;
Y_to_A1_2 := map<Y->A1 | [Y.2]>;
for c in SmallHeightRationals(300) do
	try
		Y_pts join:= Points(Pullback(Y_to_A1_1, A1![c]));
		Y_pts join:= Points(Pullback(Y_to_A1_2, A1![c]));
	catch e;
	end try;
end for;
return Y_pts;
end function;

RationalPoints_genus0 := function(affine_plane_curve)
	Y := affine_plane_curve;
	X := ProjectiveClosure(Y);
	"Attempting easy parametrization";
	for pt in PointSearch(X,30) do
		try
			P1_to_X := ImproveParametrization(Parametrization(X,pt));
			"Curve parametrized";
			return true, P1_to_X;
		catch e;
		end try;
	end for;
	"Easy parametrization failed";
	"Computing birational conic";
	C, X_to_C := Conic(X);
	"Checking for rational point on conic";
	has_point, pt := HasRationalPoint(C);
	if has_point then
		"Conic is rational";
		"Parametrizing conic";
		P1_to_C := ImproveParametrization(Parametrization(C,pt));
		"Curve parametrized";
		return true, P1_to_C*Inverse(X_to_C);
	end if;
	"Conic has no rational point";
	"Building set of points on curve";
	Y_pts := {@ @};
	for p in BasePoints(X_to_C) do
		if p[3] ne 0 then
			Include(~Y_pts, Y ! [p[1]/p[3],p[2]/p[3]]);
		end if;
	end for;
	return true, Y_pts;
end function;

LowDegreePoints := function(affine_plane_curve:quadratic:=true)
	"Building list of rational points";
	Y := affine_plane_curve;
	X := ProjectiveClosure(Y);
	Y_pts := [* *];
	for pt in CurveSearch(Y,10^3) do
		Append(~Y_pts,Coordinates(X!pt));
	end for;
	if quadratic then
		"Building list of quadratic points";
		Y_poly := DefiningPolynomial(Y);
		R := PolynomialRing(Rationals());
		for i in [1,2] do
			for r in SmallHeightRationals(10) do
				if i eq 1 then
					Y_poly_specialized := Evaluate(Y_poly,[R.1,r]);
				else
					Y_poly_specialized := Evaluate(Y_poly,[r,R.1]);
				end if;
				if Y_poly_specialized ne 0 and Degree(Y_poly_specialized) ne 0 then
					for factor in Factorization(Y_poly_specialized) do
						if Degree(factor[1]) eq 2 then
							L := NumberField(factor[1]);
							YL := BaseChange(Y,L);
							if i eq 1 then
								YL_pt := YL ! [L.1,r];
							else
								YL_pt := YL ! [r,L.1];
							end if;
							Append(~Y_pts,Coordinates(YL_pt));
						end if;
					end for;
				end if;
			end for;
		end for;
	end if;
	return Y_pts;
end function;

RationalPoints_genus1 := function(affine_plane_curve, height_bound : pointsearch:=false)
	Y := affine_plane_curve;
	"Computing birational elliptic curve";
	for pt in LowDegreePoints(Y) do
		L := Universe(pt);
		YL := BaseChange(Y,L);
		XL := ProjectiveClosure(YL);
		try
			E, XL_to_E := EllipticCurve(XL,XL ! pt);
			rank, proved := Rank(E);
			if proved then
				if rank gt 0 then
					"Curve has positive rank";
					if L eq Rationals() then
						"Computing minimal model";
						Emin, E_to_Emin := MinimalModel(E);
						YL_to_XL := map<YL->XL|[YL.1,YL.2,1]>;
						YL_to_Emin := YL_to_XL*XL_to_E*E_to_Emin;
						return true, YL_to_Emin;
					else
						return true, XL_to_E;
					end if;
				else
					"Curve has rank 0";
					"Computing torsion group";
					torsion_group, torsion_map := TorsionSubgroup(E);
					E_pts := {torsion_map(p):p in torsion_group};
					"Building set of points on curve";
					XL_pts := BasePoints(XL_to_E);
					for p in E_pts do
						try
							XL_pts join:= Points(Pullback(XL_to_E,p));
						catch e;
						end try;
					end for;
					X_pts := {};
					for p in XL_pts do
						is_rational := true;
						for c in Coordinates(p) do
							if c notin Rationals() then
								is_rational := false;
								break c;
							end if;
						end for;
						if is_rational then Include(~X_pts,p); end if;
					end for;
					Y_pts := {@ @};
					for p in X_pts do
						if p[3] ne 0 then
							Include(~Y_pts, Y ! [p[1]/p[3],p[2]/p[3]]);
						end if;
					end for;
					return true, Y_pts;
				end if;
			end if;
		catch e;
		end try;
	end for;
	"Unable to determine rational points";
	if not pointsearch then
		return false,false;
	end if;
	"Searching for points";
	return false, CurveSearch(Y, height_bound);
end function;

HasRealRoot := function(polynomial)
	f := ChangeRing(polynomial,Rationals());
	for p in Factorization(f) do
		r,_:= Signature(NumberField(p[1]));
		if r ne 0 then
			return true;
		end if;
	end for;
	return false;
end function;

CoverData := function(polynomial)
	f := ChangeRing(polynomial,Integers());
	factors := {@ p[1]: p in Factorization(f) | Degree(p[1]) gt 0 @};
	d := #factors;
	zeros := <0 : i in [1..d]>;
	ones := <1 : i in [1..d]>;
	cover_data := [* *];
	divisor_pairs := {};
	for tup in CartesianPower({0,1},d) do
		if tup notin {zeros,ones} then
			factor1 := Parent(f) ! 1;
			for i in [1..d] do
				factor1 *:= factors[i]^tup[i];
			end for;
			if IsEven(Degree(factor1)) then
				factor2 := ExactQuotient(f,factor1);
				if Maximum({Degree(factor1),Degree(factor2)}) gt 4 then
					if {factor1,factor2} notin divisor_pairs then
						Include(~divisor_pairs,{factor1,factor2});
						resultant_radical := 1;
						for pair in Factorization(Resultant(factor1,factor2)) do
							resultant_radical *:= pair[1];
						end for;
						divisors := Divisors(resultant_radical);
						if not HasRealRoot(factor1) then
							sign := Sign(Evaluate(factor1,0));
							twists := {sign*d : d in divisors};
						elif not HasRealRoot(factor2) then
							sign := Sign(Evaluate(factor2,0));
							twists := {sign*d : d in divisors};
						else
							twists := {};
							for d in divisors do
								twists join:= {d,-d};
							end for;
						end if;
						Append(~cover_data, <[factor1,factor2],twists>);
					end if;
				end if;
			end if;
		end if;
	end for;
	return cover_data;
end function;

forward RationalPoints_hyperelliptic;

RationalPoints_via_covers := function(hyperelliptic_curve)
	"Analyzing covers";
	X := hyperelliptic_curve;
	X_pts := PointsAtInfinity(X);
	f,_ := HyperellipticPolynomials(X);
	if not IsIrreducible(f) then
		for cd in CoverData(f) do
			g := cd[1][1]; h := cd[1][2];
			twists := cd[2];
			G := HyperellipticCurve(g);
			H := HyperellipticCurve(h);
			X_coordinates := {};
			twists_handled := true;
			for d in twists do
				g_success := false;
				h_success := false;
				if Degree(g) gt 4 then
					Gd := QuadraticTwist(G,d);
					proved, Gd_pts := RationalPoints_hyperelliptic(Gd);
					if proved then
						g_success := true;
						for p in Gd_pts do
							if p[3] ne 0 then
								Include(~X_coordinates, p[1]/p[3]);
							end if;
						end for;
					end if;
				else
					Hd := QuadraticTwist(H,d);
					proved, Hd_pts := RationalPoints_hyperelliptic(Hd);
					if proved then
						h_success := true;
						for p in Hd_pts do
							if p[3] ne 0 then
								Include(~X_coordinates, p[1]/p[3]);
							end if;
						end for;
					end if;
				end if;
				if not g_success and not h_success then
					twists_handled := false;
					break d;
				end if;
			end for;
			if twists_handled then
				for c in X_coordinates do
					is_square, root := IsSquare(Evaluate(f,c));
					if is_square then
						X_pts join:= {@ X ! [c,root], X ! [c,-root] @};
					end if; 
				end for;
				return true, X_pts;
			end if;
		end for;
	end if;
	"Argument via covers failed";
	return false,_;
end function;

RationalPoints_via_quotients := function(affine_plane_curve)
	Y := affine_plane_curve;
	X := ProjectiveClosure(Y);
	"Computing automorphism group";
	G := AutomorphismGroup(X);
	for g in Automorphisms(X) do
		success := false;
		if Order(G ! g) gt 1 then
			H := AutomorphismGroup(X,[G ! g]);
			"Computing quotient";
			quo, quo_map := CurveQuotient(H);
			genus := Genus(quo);"Quotient has genus", genus;
			X_pts := BasePoints(quo_map);
			if IsConic(quo) and not HasRationalPoint(Conic(quo)) then
				success := true;
				quo_pts := {};
			elif genus eq 1 then
				if Type(quo) eq CrvEll then
					"Quotient is elliptic";
					rank, proved := Rank(quo);
					if proved and rank eq 0 then 
						torsion_group, torsion_map := TorsionSubgroup(quo);
						quo_pts := {torsion_map(p): p in torsion_group};
						success := true;
					end if;
				else
					for pt in PointSearch(quo,10^3) do
						if IsNonsingular(pt) then
							E, quo_to_E := EllipticCurve(quo,pt);
							rank, proved := Rank(E);
							if proved and rank eq 0 then 
								torsion_group, torsion_map := TorsionSubgroup(E);
								E_pts := {torsion_map(p): p in torsion_group};
								quo_pts := {Pullback(quo_to_E,p): p in E_pts};
								success := true; break pt;
							end if;
						end if;
					end for;
				end if;
			elif genus gt 1 and IsHyperellipticCurve(quo) then
				"Quotient is hyperelliptic";
				success, quo_pts := RationalPoints_hyperelliptic(quo);
			end if;
			if success then
				for pt in quo_pts do
					X_pts join:= Points(Pullback(quo_map, pt));
				end for;
				Y_pts := {@ Y ! [pt[1]/pt[3],pt[2]/pt[3]] : pt in X_pts | pt[3] ne 0 @};
				return true, Y_pts;
			end if;
		end if;
	end for;
	"Quotient argument failed";
	return false,_;
end function;

ChabautyBound := function(hyper_poly,bad_primes)
	f := Qx ! hyper_poly;
	precision := 20;
	upper_bounds := {};
	for p in PrimesInInterval(2,20) do
		if p notin bad_primes then
			try
				c_data := coleman_data(Qxy.1^2 - f,p,precision);
				c_bound := #effective_chabauty(c_data:bound:=10^5,e:=50);
				Include(~upper_bounds,c_bound);
			catch e;
			end try;
		end if;
	end for;
	if #upper_bounds gt 0 then
		return true, Minimum(upper_bounds);
	end if;
	return false,_;
end function;

RationalPoints_via_Chabauty := function(hyperelliptic_curve,curve_points)
	"Attempting Chabauty argument";
	X := hyperelliptic_curve;
	X_poly,_ := HyperellipticPolynomials(X);
	X_pts := curve_points;
	J := Jacobian(X);
	"Computing Jacobian rank bound";
	rb := RankBound(J);
	"Rank is at most", rb;
	if rb eq 0 and Genus(X) eq 2 then
	"Applying MAGMA rank 0 Chabauty";
		return true, Chabauty0(J);
	end if;
	if rb lt Genus(X) then
		if Genus(X) eq 2 then
				"Applying MAGMA Chabauty";
				for J_pt in Points(J:Bound:=1000) do
					if Order(J_pt) eq 0 then
						"Chabauty argument complete";
						return true, Chabauty(J_pt);
					end if;
				end for;
		end if;
		"Computing Chabauty bound";
		have_bound, bound := ChabautyBound(X_poly,BadPrimes(X));
		if have_bound and #X_pts eq bound then
			return true, X_pts;
		end if;
	end if;
	"Chabauty argument failed";
	return false,_;
end function;

RationalPoints_hyperelliptic := function(hyperelliptic_curve)
	C := hyperelliptic_curve;
	X, C_to_X := SimplifiedModel(C);
	"Searching for rational points on hyperelliptic curve";
	X_search := Points(X: Bound:=10^3);
	if #X_search eq 0 then
		"No points found\nAttempting to rule out rational points";
		X_poly,_ := HyperellipticPolynomials(X);
		local_obstruction := not HasPointsEverywhereLocally(X_poly,2);
		ruled_out := local_obstruction or #TwoCoverDescent(X) eq 0;
		if ruled_out then
			"Hyperelliptic curve has no rational point"; 
			return true, {@ @};
		end if;	
	else 
		success, X_pts := RationalPoints_via_covers(X);
		if success then
			C_pts := {@ Pullback(C_to_X,pt): pt in X_pts @};
			return true, C_pts;
		end if;
		f,_ := HyperellipticPolynomials(X);
		AA := AffineSpace(Rationals(),2);
		Y := Curve(AA, AA.2^2 - Evaluate(f,AA.1));
		"Searching for quotients of curve";
		success, Y_pts := RationalPoints_via_quotients(Y);
		if success then
			X_pts := PointsAtInfinity(X);
			X_pts join:= {@ X ! Coordinates(pt) : pt in Y_pts @};
			C_pts := {@ Pullback(C_to_X,pt): pt in X_pts @};
			return true, C_pts;
		end if;
		success, X_pts := RationalPoints_via_Chabauty(X,X_search);
		if success then
			C_pts := {@ Pullback(C_to_X,pt): pt in X_pts @};
			return true, C_pts;
		end if;
	end if;		
	return false,_;
end function;

RationalPoints_irreducible := function(affine_plane_curve, height_bound : search:=false)
	Y := affine_plane_curve;
	assert HasFunctionField(Y);
	"Curve is irreducible";
	"Computing genus";
	g := Genus(Y);
	"Curve has genus", g;
	"Checking for geometrical reducibility";
	if not IsAbsolutelyIrreducible(Y) then
		"Curve is geometrically reducible";
		return true, SingularPoints(Y);
	end if;
	"Curve is geometrically irreducible";
	if g eq 0 then return RationalPoints_genus0(Y); end if;
	if g eq 1 then return RationalPoints_genus1(Y,height_bound : pointsearch:=search); end if;
 
	is_geom_hyper, C, Y_to_C := IsGeometricallyHyperelliptic(Y);
	if is_geom_hyper then
		"Curve is geometrically hyperelliptic";
		"Computing conic quotient";
		quo := Conic(C);
		"Checking for rational point on conic";
		if not HasRationalPoint(quo) then
			"Conic has no rational point";
			return true, BasePoints(Y_to_C);
		else
		"Conic has rational points";
		"Curve is hyperelliptic";
		"Computing hyperelliptic equation";
			is_hyper,X,Y_to_X := IsHyperelliptic(Y);
			proved, X_pts := RationalPoints_hyperelliptic(X);
			if proved then
				Y_pts := BasePoints(Y_to_X);
				for pt in X_pts do
					Y_pts join:= Points(Pullback(Y_to_X,pt));
				end for;
				return true, Y_pts;
			end if;
		end if;
	else
		"Curve is not geometrically hyperelliptic";
		"Searching for quotients of curve";
		proved, Y_pts := RationalPoints_via_quotients(Y);
		if proved then return true, Y_pts; end if;
	end if;
"Unable to determine rational points";
if not search then
	return false,false;
end if;
"Searching for points";
return false, CurveSearch(Y, height_bound);
end function;

CurvePoints := function(affine_plane_curve: search_bound:=10^5, do_search:=false)
	Y := affine_plane_curve;
	factors := {@ f[1] : f in Factorization(DefiningPolynomial(Y)) @};
	points_data := [* *];
	for f in factors do
		proved, description := RationalPoints_irreducible(Curve(AmbientSpace(Y),f),search_bound: search:= do_search);
		Append(~points_data, <proved, description>);
	end for;
	return points_data;
end function;
