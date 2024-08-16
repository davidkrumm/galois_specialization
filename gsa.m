load "CurvePoints.m";

Specialize := function(poly,c)
	R := Parent(poly);
	specialized_poly := Evaluate(Polynomial([Evaluate(coeff,c) : coeff in Coefficients(poly)]), R.1);
	return specialized_poly;
end function;

IsBoundedAbove := function(node, classes)
	for i in classes do
		if node le i then
			return true;
		end if;
	end for;
	return false;
end function;

t_Parametrization := function(description)
	Y := Codomain(description);
	DE := DefiningEquations(description);
	f := DE[1]/DE[3];
	return Evaluate(f,[Y.1,1]);
end function;

IntersectParametrizations := function(description1, description2)
	f := t_Parametrization(description1); Numf:= Numerator(f); Denf:= Denominator(f);
	g := t_Parametrization(description2); Numg:= Numerator(g); Deng:= Denominator(g);
	AA := AffineSpace(Rationals(),2);
	Nf := Evaluate(Numf,[AA.1,1,1]);
	Df := Evaluate(Denf,[AA.1,1,1]); 
	Ng := Evaluate(Numg,[AA.2,1,1]);
	Dg := Evaluate(Deng,[AA.2,1,1]);
	return Curve(AA,Nf*Dg - Ng*Df),Nf,Df;
end function;

forward GSAp;

GSA := function(polynomial)
"\nComputing generic Galois group";
G,_,S := GaloisGroup(polynomial);
"Computing lattice of subgroups";
Gsubs := SubgroupLattice(G);
e,r,u,c := GSAp(polynomial,G,S,Gsubs);
return e,r,u;
end function;

GSAp := function(poly,galois_group,galois_data,lattice : search_bound:=10^5, dis:=[], node_equation:=false)
	lc := LeadingCoefficient(poly);
	theta := SquarefreePart(poly);
	disc := Discriminant(theta);
	assert disc ne 0;
	M := Degree(theta); SM := Sym(M);
	exceptional_set := {r[1]: r in Roots(disc*lc)};
	G := galois_group; Gsubs := lattice; S := galois_data;
	"Hasse diagram has", #Gsubs, "nodes";
	realized_SM_classes := [* *]; // subgroups of SM realized as specializations of G
	unknown_nodes := [* *]; // nodes that could not be realized nor ruled out
	proved_finite := [* *]; // nodes occurring finitely many times, all known
	proved_infinite := [* *]; //nodes proved to occur infinitely often
	proved_parametrizable := [* *]; //nodes whose associated curve is proved rational
	handled_curves := [* *]; //nodes whose rational points were determined
	finite_intersections := [* *]; //pairs of nodes whose intersection is proved finite
	
	Y := function(H)
		qH := GaloisSubgroup(S, H);
		assert {Denominator(c): c in Coefficients(qH)} eq {1};
		AA := AffineSpace(Rationals(),2);
		poly := Polynomial([Evaluate(Numerator(c), AA.1) : c in Coefficients(qH)]);
		f := Evaluate(poly, AA.2);
		return Curve(AA,f),qH;
	end function;

	Realize := procedure(node,curve,poly,~proved_infinite,~realized_SM_classes)
		h := node; H := Group(h);
		YH := curve; qH := poly;
		test_values := {r[1] : r in Roots(Numerator(Discriminant(qH)))};
		test_values join:= {j : j in SmallHeightRationals(5)};
		"First attempt";
		for c in test_values diff exceptional_set do
			try 
				Gc := GaloisGroup(Specialize(theta,c));
				if IsConjugate(SM,Gc,H) then
					"Node realized";
					Append(~realized_SM_classes, <c,H>);
					break;
				end if;
			catch e;
			end try;
		end for;
		is_realized := H in {i[2]: i in realized_SM_classes};
		if not is_realized then
			"Second attempt";
			test_values := {pt[1] : pt in PointSearch(YH,10^3)};
			for c in test_values diff exceptional_set do
				try 
					Gc := GaloisGroup(Specialize(theta,c));
					if IsConjugate(SM,Gc,H) then
						"Node realized";
						Append(~realized_SM_classes, <c,H>);
						break;
					end if;
				catch e;
				end try;
			end for;
			is_realized := H in {i[2]: i in realized_SM_classes};
			if not is_realized then
				"Third attempt";
				test_values := {};
				for i in proved_infinite do
					class := i[1]; map := i[2];
					Yi, qi := Y(Group(class)); 
					if h le class then
						crv := Domain(map); // an elliptic curve or P^1
						if Genus(crv) eq 1 then
							for r in PointSearch(crv,10) do
								try
									pt := map(r);
									if pt[3] ne 0 then
										c := pt[1]/pt[3];
										assert HasRoot(Specialize(qi,c));
										if HasRoot(Specialize(qH,c)) then
											Include(~test_values,c);
										end if;
									end if; "Elliptic!";
								catch e;
								end try;
							end for;
						else
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
				for c in test_values diff exceptional_set do
					try
						Gc := GaloisGroup(Specialize(theta,c));
						if IsConjugate(SM,Gc,H) then
							"Node realized";
							Append(~realized_SM_classes, <c,H>);
							break;
						end if;
					catch e;
					end try;
				end for;
			end if;
		end if;
		is_realized := H in {i[2]: i in realized_SM_classes};
		if not is_realized then "Node not realized"; end if;
	end procedure;
	
	ClassifyNode := procedure(node,~realized_SM_classes,~unknown_nodes,~handled_curves,~proved_finite,~proved_infinite,~proved_parametrizable,~finite_intersections)
		h := node; H := Group(h);
		"Computing curve equation";
		YH, qH := Y(H);
		"Attempting to realize node";
		Realize(h,YH,qH,~proved_infinite,~realized_SM_classes);
		"Analyzing set of rational points";
		proved, description := RationalPoints_irreducible(YH,search_bound);
		is_realized := H in {i[2]: i in realized_SM_classes};
		if not proved and not is_realized then
			"Unable to classify node";
			if node_equation then
				Append(~unknown_nodes,<H,YH>);
			else
				Append(~unknown_nodes,H);
			end if;
		end if;
		if proved then
			Append(~handled_curves,<H,description>);
			if Type(description) eq SetIndx then
				"Node proved finite";
				Append(~proved_finite,h);
				"Classifying nodes below";
				for c in {pt[1] : pt in description} diff exceptional_set do
					Gc := GaloisGroup(Specialize(theta,c));
					is_new_SM_class := forall{j:j in realized_SM_classes|not IsConjugate(SM,Gc,j[2])};
					if is_new_SM_class then
						Append(~realized_SM_classes, <c,Gc>);
					end if;
				end for;
			else
				"Node proved infinite";
				Append(~proved_infinite,<h,description>);
				if Genus(Domain(description)) eq 0 then
					for i := 1 to #proved_parametrizable do
						other_node := proved_parametrizable[i][1];
						if not h le other_node then
							"Intersecting nodes",h,"and",other_node;
								map_from_P1 := proved_parametrizable[i][2];
								meet_curve,num,den := IntersectParametrizations(description,map_from_P1);
								if IsIrreducible(meet_curve) then
									proof, desc := RationalPoints_irreducible(meet_curve,search_bound);
									if proof and Type(desc) eq SetIndx then
										"Intersection proved finite";
										Append(~finite_intersections,<h,other_node>);
										"Classifying nodes below";
										for pt in desc do
											c_num := Evaluate(num,[pt[1],pt[2]]);
											c_den := Evaluate(den,[pt[1],pt[2]]);
											if c_den ne 0 then
												c := c_num/c_den;
												if c notin exceptional_set then
													Gc := GaloisGroup(Specialize(theta,c));
													is_new_SM_class := forall{j:j in realized_SM_classes|not IsConjugate(SM,Gc,j[2])};
													if is_new_SM_class then
														Append(~realized_SM_classes, <c,Gc>);
													end if;
												end if;
											end if;
										end for;
									end if;
								else //meet_curve is reducible
									cp := CurvePoints(meet_curve);
									if forall{u : u in cp | u[1]} and forall{u : u in cp | Type(u[2]) eq SetIndx} then
										"Intersection proved finite";
										Append(~finite_intersections,<h,other_node>);
										"Classifying nodes below";
										for u in cp do
											for pt in u[2] do
												c_num := Evaluate(num,[pt[1],pt[2]]);
												c_den := Evaluate(den,[pt[1],pt[2]]);
												if c_den ne 0 then
													c := c_num/c_den;
													if c notin exceptional_set then
														Gc := GaloisGroup(Specialize(theta,c));
														is_new_SM_class := forall{j:j in realized_SM_classes|not IsConjugate(SM,Gc,j[2])};
														if is_new_SM_class then
															Append(~realized_SM_classes, <c,Gc>);
														end if;
													end if;
												end if;
											end for;
										end for;
									end if;
								end if;
							end if;
					end for;
					Append(~proved_parametrizable,<h,description>);
				end if;
			end if;
		end if;
	end procedure;


   //// Main steps of GaloisSpecialization
   
  "Realizing top node";
  top_realized := false;
	for c in SmallHeightRationals(10) do
		if c notin exceptional_set then
			Gc := GaloisGroup(Specialize(theta,c));
			if Order(Gc) eq Order(G) then
				Append(~realized_SM_classes, <c,Gc>);
				top_realized := true;
				break;
			end if;
		end if;
	end for;
	assert top_realized;
	"Top node realized";
   
	//// Breadth-first traversal of Gsubs 
	visited := [Gsubs ! G];
	queue := [* <Gsubs ! G,0> *];
	while #queue ne 0 do
		h := queue[1][1]; H := Group(h);
		if h in dis then
			"\nClassifying node", h, "as unknown";
			if node_equation then
				"Computing curve equation";
				Append(~unknown_nodes,<H,Y(H)>);
			else
				Append(~unknown_nodes,H);
			end if;
		else
			depth := queue[1][2];
			if depth ne 0 then
				"\nClassifying node", h;
				"Node depth:", depth;
				is_new_SM_class := forall(i){j:j in realized_SM_classes|not IsConjugate(SM,H,j[2])};
				is_below_finite_intersection := false;
				for node_pair in finite_intersections do
					if h le node_pair[1] and h le node_pair[2] then
						is_below_finite_intersection := true;
						break;
					end if;
				end for;
				if not is_new_SM_class or IsBoundedAbove(h,proved_finite) or is_below_finite_intersection then
					"Node classified previously";
				else
					ClassifyNode(h,~realized_SM_classes,~unknown_nodes,~handled_curves,~proved_finite,~proved_infinite,~proved_parametrizable,~finite_intersections);
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
	return exceptional_set, realized_SM_classes, unknown_nodes, handled_curves;
end function;

SpecializationData := function(realized, unknown)
	groups := {p[2]: p in realized};
	if #unknown gt 0 then
		if #unknown[1] eq 2 then
			groups join:= {p[1] : p in unknown};
		else
			groups join:= {p : p in unknown};
		end if;
	end if;
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
