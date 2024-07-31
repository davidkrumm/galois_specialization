load "CurvePoints.m";

Specialize := function(poly,v)
	R := Parent(poly);
	sp_poly := Evaluate(Polynomial([Evaluate(c,v) : c in Coefficients(poly)]), R.1);
	return sp_poly;
end function;

IsBoundedAbove := function(node, classes)
	for i in classes do
		if node le i then
			return true;
		end if;
	end for;
	return false;
end function;

GSA := function(polynomial : search_bound:=10^5)
	theta := SquarefreePart(polynomial);
	disc := Discriminant(theta);
	assert disc ne 0;
	lc := LeadingCoefficient(theta);
	M := Degree(theta); SM := Sym(M);
	exceptional_set := {r[1]: r in Roots(disc*lc)};
	
	"\nComputing generic Galois group";
	G,_,S := GaloisGroup(theta);
	"Computing lattice of subgroups";
	Gsubs := SubgroupLattice(G); // Poset of conjugacy classes of subgroups of G
	"Hasse diagram has", #Gsubs, "nodes";
	realized_SM_classes := [* *]; // subgroups of SM realized as specializations of G
	unknown_nodes := [* *]; // nodes that could not be realized nor ruled out
	proved_finite := [* *]; // nodes occurring finitely many times, all known
	proved_infinite := [* *]; //nodes proved to occur infinitely often
	
	Y := function(H)
		qH := GaloisSubgroup(S, H);
		assert {Denominator(c): c in Coefficients(qH)} eq {1};
		AA := AffineSpace(Rationals(),2);
		poly := Polynomial([Evaluate(Numerator(c), AA.1) : c in Coefficients(qH)]);
		f := Evaluate(poly, AA.2);
		return Curve(AA, f), qH;
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
			test_values := {pt[1] : pt in PointSearch(YH,1000)};
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
	
	ClassifyNode := procedure(node,~realized_SM_classes,~unknown_nodes,~handled_curves,~proved_finite,~proved_infinite)
		h := node; H := Group(h);
		"Computing curve equation";
		YH, qH := Y(H);
		"Attempting to realize node";
		Realize(h,YH,qH,~proved_infinite,~realized_SM_classes);
		"Analyzing set of rational points";
		proved, description := RationalPoints_irreducible(YH,search_bound: search:=false);
		is_realized := H in {i[2]: i in realized_SM_classes};
		if not proved and not is_realized then
			"Unable to classify node";
			Append(~unknown_nodes,H);
		end if;
		if proved then
			if Type(description) eq SetIndx then
				"Node proved finite";
				Append(~proved_finite,h);
				"Classifying nodes below";
				for c in {pt[1] : pt in description} diff exceptional_set do
					Gc := GaloisGroup(Specialize(theta,c));
					is_new_SM_class := forall(i){j:j in realized_SM_classes|not IsConjugate(SM,Gc,j[2])};
					if is_new_SM_class then
						Append(~realized_SM_classes, <c,Gc>);
					end if;
				end for;
			else
				"Node proved infinite";
				Append(~proved_infinite,<h,description>);
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
   
	//// Breadth-first traversal of Gsubs 

	visited := [Gsubs ! G];
	queue := [* <Gsubs ! G,0> *];
	while #queue ne 0 do
		h := queue[1][1]; H := Group(h);
		depth := queue[1][2];
		if depth ne 0 then
			"\nClassifying node", h;
			"Node depth:", depth;
			is_new_SM_class := forall(i){j:j in realized_SM_classes|not IsConjugate(SM,H,j[2])};
			if IsBoundedAbove(h,proved_finite) or not is_new_SM_class then
				"Node classified previously";
			else 
				ClassifyNode(h,~realized_SM_classes,~unknown_nodes,~handled_curves,~proved_finite,~proved_infinite);
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
	return exceptional_set, realized_SM_classes, unknown_nodes;
end function;

SpecializationData := function(theta)
	e,r,u := GSA(theta);
	groups := {p[2]: p in r} join {p[1]: p in u};
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
