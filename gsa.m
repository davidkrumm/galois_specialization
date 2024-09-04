load "CurvePoints.m";

/* Given a polynomial p(t,x) with coefficients in the polynomial ring Q[t]
and given a rational number c, returns the specialized polynomial p(c,x). */
Specialize := function(poly,c)
	R := Parent(poly);
	_<x> := PolynomialRing(Rationals());
	specialized_poly := Evaluate(Polynomial([Evaluate(coeff,c) : coeff in Coefficients(poly)]), x);
	return specialized_poly;
end function;

t_Parametrization := function(map_from_P1)
	Y := Codomain(map_from_P1);
	DE := DefiningEquations(map_from_P1);
	f := DE[1]/DE[3];
	return Evaluate(f,[Y.1,1]);
end function;

MeetParametrizations := function(map1,map2)
	f := t_Parametrization(map1);
	g := t_Parametrization(map2);
	AA := AffineSpace(Rationals(),2);
	Nf := Evaluate(Numerator(f),[AA.1,1,1]);
	Df := Evaluate(Denominator(f),[AA.1,1,1]); 
	Ng := Evaluate(Numerator(g),[AA.2,1,1]);
	Dg := Evaluate(Denominator(g),[AA.2,1,1]);
	return Curve(AA,Nf*Dg - Ng*Df),Nf,Df;
end function;

GSAp := function(poly,galois_group,galois_data,lattice:search_bound:=10^5,skip:=[],wit:=[],print_curves:=false,g0bound:=10^9,rbound:=10^15)
	lc := LeadingCoefficient(poly); theta := SquarefreePart(poly); 
	disc := Discriminant(theta); M := Degree(theta); SM := Sym(M);
	exceptional_set := {r[1]: r in Roots(disc*lc)};
	"\nExceptional set is", exceptional_set;
	G := galois_group; Gsubs := lattice;
	"Hasse diagram has", #Gsubs, "nodes";
	realized := [* *]; // subgroups of SM realized as specializations of G
	unknown := [* *]; // nodes that could not be realized nor ruled out
	proved_finite := [* *]; // nodes proved to occur finitely many times, all of them known
	proved_infinite := [* *]; //nodes proved to occur infinitely often
	parametrized := [* *]; //nodes whose associated curve is parametrized
	rat_pts := [* *]; //nodes whose rational points were successfully computed
	finite_meets := [* *]; //pairs of nodes whose meet is proved finite
	
	Y := function(H)
		qH := GaloisSubgroup(galois_data,H);
		assert {Denominator(c): c in Coefficients(qH)} eq {1};
		AA := AffineSpace(Rationals(),2);
		poly := Polynomial([Evaluate(Numerator(c), AA.1) : c in Coefficients(qH)]);
		f := Evaluate(poly, AA.2);
		return Curve(AA,f),qH;
	end function;

	RealizesGroup := function(test_values,group)
		for c in test_values diff exceptional_set do
			Gc := GaloisGroup(Specialize(theta,c));
			if IsConjugate(SM,Gc,group) then
				return true,c;
			end if;
		end for;
		return false,0;
	end function;
	
	forward RealizeByParents;

	RealizeNode := procedure(node,curve,poly,~realized,~proved_infinite)
		h := node; H := Group(h);
		is_realized := exists{i:i in realized|IsConjugate(SM,H,i[2])};
		if is_realized then 
			"Node realized previously";
		else
			YH := curve; qH := poly;
			test_values := {r[1] : r in Roots(Numerator(Discriminant(qH)))};
			"First attempt";
			is_realized,c := RealizesGroup(test_values,H);
			if is_realized then
				"Node realized by", c;
				Append(~realized, <c,H>);
			else
				RealizeByParents(h,qH,~realized,~is_realized,~proved_infinite);
			end if;
			if not is_realized then
				coeff_bound := Maximum({AbsoluteValue(co): co in Coefficients(DefiningPolynomial(YH))});
				if coeff_bound gt rbound then
					"Curve equation exceeds bounds";
				else
					"Second attempt";
					test_values := {pt[1] : pt in CurveSearch(YH,1,30)};
					is_realized,c := RealizesGroup(test_values,H);
					if is_realized then
						"Node realized by", c;
						Append(~realized, <c,H>);
					else
						"Third attempt";
						test_values := {pt[1] : pt in CurveSearch(YH,10^3,50)};
						is_realized,c := RealizesGroup(test_values,H);
						if is_realized then
							"Node realized by", c;
							Append(~realized, <c,H>);
						else
							"Node not realized";
						end if;
					end if;
				end if;
			end if;
		end if;
	end procedure;
	
	RealizeByParents := procedure(node,poly,~realized,~is_realized,~proved_infinite)
		h := node; H := Group(h); qH := poly;					
		test_values := {};
		for i in proved_infinite do
			some_node := i[1]; map := i[2];
			Yi, qi := Y(Group(some_node)); 
			if h le some_node then
				crv := Domain(map); // an elliptic curve or P^1
				if Genus(crv) eq 0 then
					for r in SmallHeightRationals(10) do
						pt := map(crv![r,1]);
						if pt[3] ne 0 then
							c := pt[1]/pt[3];
							assert HasRoot(Specialize(qi,c));
							if HasRoot(Specialize(qH,c)) then
								Include(~test_values,c);
							end if;
						end if;
					end for;
				end if;
			end if;
		end for;
		is_realized,c := RealizesGroup(test_values,H);
		if is_realized then
			"Node realized by", c;
			Append(~realized, <c,H>);
		end if;
	end procedure;
	
	RealizeByMap := procedure(group,map,~realized)
		curve := Domain(map);
		if Genus(curve) eq 0 then
			test_values := {};
			for r in SmallHeightRationals(5) do
				pt := map(curve![r,1]);
				if pt[3] ne 0 then
					c := pt[1]/pt[3];
					Include(~test_values,c);
				end if;
			end for;
			node_realized,c := RealizesGroup(test_values,group);
			assert node_realized; 
			"Node realized by", c;
			Append(~realized, <c,group>);
		else 
			"IMPLEMENT this case";
		end if;
	end procedure;
	
	IntersectNodes := procedure(node,node_map,~parametrized,~finite_meets,~realized)
		h := node;
		for i := 1 to #parametrized do
			other_node := parametrized[i][1];
			if not h le other_node then
				"Intersecting nodes",h,"and",other_node;
				map_from_P1 := parametrized[i][2];
				meet_curve,num,den := MeetParametrizations(node_map,map_from_P1);
				cp := CurvePoints(meet_curve);
				if forall{u : u in cp | u[1] and Type(u[2]) eq SetIndx} then
					"Intersection proved finite";
					Append(~finite_meets,<h,other_node>);
					"Classifying nodes below";
					for u in cp do
						for pt in u[2] do
							c_num := Evaluate(num,[pt[1],pt[2]]);
							c_den := Evaluate(den,[pt[1],pt[2]]);
							if c_den ne 0 then
								c := c_num/c_den;
								if c notin exceptional_set then
									Gc := GaloisGroup(Specialize(theta,c));
									is_realized_group := exists{i:i in realized|IsConjugate(SM,Gc,i[2])};
									if not is_realized_group then Append(~realized, <c,Gc>); end if;
								end if;
							end if;
						end for;
					end for;
				end if;
			end if;
		end for;
	end procedure;
	
	ClassifyNode := procedure(node,~realized,~unknown,~rat_pts,~proved_finite,~proved_infinite,~parametrized,~finite_meets,~print_curves)
		h := node; H := Group(h);
		"Computing curve equation";
		YH,qH := Y(H);
		"Attempting to realize node";
		RealizeNode(h,YH,qH,~realized,~proved_infinite);
		node_realized := exists{i:i in realized|IsConjugate(SM,H,i[2])};
		"Analyzing set of rational points";
		proved, description := RationalPoints_irreducible(YH,search_bound: genus0bound:=g0bound);
		if not proved and not node_realized then
			Append(~unknown,H);
			if print_curves then
				_<a,b> := PolynomialRing(Rationals(),2);
				"Node curve:", Evaluate(DefiningPolynomial(Y(Group(h))),[a,b]);
			end if;
		end if;
		if proved then
			Append(~rat_pts,<H,description>);
			if Type(description) eq SetIndx then
				"Node proved finite";
				Append(~proved_finite,h);
				"Classifying nodes below";
				for c in {pt[1] : pt in description} diff exceptional_set do
					Gc := GaloisGroup(Specialize(theta,c));
					is_realized_group := exists{i:i in realized|IsConjugate(SM,Gc,i[2])};
					if not is_realized_group then
						Append(~realized, <c,Gc>);
					end if;
				end for;
			else
				"Curve proved infinite";
				Append(~proved_infinite,<h,description>);
				if not node_realized then
					"Realizing node"; RealizeByMap(Group(h),description,~realized);
				end if;
				if Genus(Domain(description)) eq 0 then
					IntersectNodes(h,description,~parametrized,~finite_meets,~realized);
					Append(~parametrized,<h,description>);
				end if;
			end if;
		end if;
	end procedure;


							 //// Main steps of the Galois specialization algorithm ////
  
  // Compute G_c for c up to height 10
  "Computing small height specializations";
  c_values := {c: c in SmallHeightRationals(10)} join {c: c in wit};
  for c in c_values do
		if c notin exceptional_set then
			Gc := GaloisGroup(Specialize(theta,c));
			is_realized_group := exists{i:i in realized|IsConjugate(SM,Gc,i[2])};
			if not is_realized_group then
				Append(~realized, <c,Gc>);
			end if;
		end if;
  end for;
  #realized, "groups realized";
  
  // Realizing G as a specialization G_c
  top_realized := exists{i:i in realized|Order(i[2]) eq Order(G)};
	assert top_realized;
	"Top node realized";
   
	//// Breadth-first traversal of the lattice of subgroups of G 
	visited := [Gsubs ! G];
	queue := [* <Gsubs ! G,0> *];
	while #queue ne 0 do
		h := queue[1][1]; depth := queue[1][2];
		if h in skip then
			"\nSkipping node", h;
			is_realized_group := exists{i:i in realized|IsConjugate(SM,Group(h),i[2])};
			if not is_realized_group then Append(~unknown,Group(h)); end if;
			if print_curves then
			_<a,b> := PolynomialRing(Rationals(),2);
				"Node curve:", Evaluate(DefiningPolynomial(Y(Group(h))),[a,b]);
			end if;
		else // h is not skipped
			if depth ne 0 then
				"\nClassifying node", h;
				"Node depth:", depth;
				is_below_finite_node := exists{i:i in proved_finite | h le i};
				is_below_finite_meet := exists{i:i in finite_meets | h le i[1] and h le i[2]};
				if is_below_finite_node or is_below_finite_meet then
					"Node classified previously";
				else
					ClassifyNode(h,~realized,~unknown,~rat_pts,~proved_finite,~proved_infinite,~parametrized,~finite_meets,~print_curves);
				end if;
			end if;
		end if;
		is_realized_group := exists{i:i in realized|IsConjugate(SM,Group(h),i[2])};
		is_unknown_group := exists{i:i in unknown|IsConjugate(SM,Group(h),i)};
		is_conjugate_to_skipped := exists{i:i in skip|IsConjugate(SM,Group(h),Group(Gsubs!i))};
		if is_realized_group then 
			if depth ne 0 then "Node is realized"; end if;
		else
			if is_unknown_group then
				"Node is unknown";
			else
				if is_conjugate_to_skipped then
					"Node is unrealizable or skipped";
				else
					"Node is unrealizable";
				end if;
			end if;
		end if;
		Remove(~queue,1);
		for m in MaximalSubgroups(h) do
			if m notin visited then
				Append(~visited,m);
				Append(~queue,<m,depth+1>);
			end if;
		end for;
	end while;
	"\nRealized",#realized,"groups";
	"Unknown nodes:", unknown;
	return exceptional_set,realized,unknown,rat_pts;
end function;

GSA := function(poly : pc:=false)
	"\nComputing generic Galois group";
	G,_,S := GaloisGroup(poly);
	"Computing lattice of subgroups";
	Gsubs := SubgroupLattice(G);
	e,r,u,c := GSAp(poly,G,S,Gsubs: print_curves:=pc);
	return e,r,u;
end function;

SpecializationData := function(realized,unknown)
	groups := {p[2]: p in realized} join {u : u in unknown};
	factorization_types := {};
	densities := {};
	for gp in groups do
		Include(~factorization_types,{* #o : o in Orbits(gp) *});
	end for;
	for gp in groups do
		stabilizer_union := {};
		for i := 1 to #GSet(gp) do
			stabilizer_union join:= ElementSet(gp, Stabilizer(gp, i));
		end for;
		Include(~densities,#stabilizer_union/#gp);
	end for;
	return groups, factorization_types, densities;
end function;
