load "CurvePoints.m";

/* Given a polynomial p(t,x) with coefficients in the polynomial ring Q[t]
and given a rational number c, returns the specialized polynomial p(c,x) */
Specialize := function(poly,c)
	R := Parent(poly);
	_<x> := PolynomialRing(Rationals());
	specialized_poly := Evaluate(Polynomial([Evaluate(coeff,c) : coeff in Coefficients(poly)]), x);
	return specialized_poly;
end function;

/* The main function for GSA. */
GSAp := function(poly,galois_group,galois_data,poset: search_bound:=10^5,skip:=[],wit:=[],g0bound:=10^25)
	
	theta := SquarefreePart(poly); M := Degree(theta); SM := Sym(M);
	exceptional_set := {r[1]: r in Roots(LeadingCoefficient(poly)*Discriminant(theta))};
	"\nExceptional set is", exceptional_set;
	G := galois_group; Gsubs := poset;
	"Hasse diagram has", #Gsubs, "nodes";
	
	nodes_finite := [* *];
	nodes_infinite := [* *];
	node_pairs_finite := [* *];
	known_groups := [* *];
	
	/* Returns the curve Y_H corresponding to a subgroup H of G
	as well as the defining polynomial q_H of the fixed field of H */
	Y := function(H)
		qH := GaloisSubgroup(galois_data,H);
		assert LeadingCoefficient(qH) eq 1;
		assert {Denominator(co): co in Coefficients(qH)} eq {1};
		AA := AffineSpace(Rationals(),2);
		poly := Polynomial([Evaluate(Numerator(co), AA.1) : co in Coefficients(qH)]);
		f := Evaluate(poly, AA.2);
		return Curve(AA,f),qH;
	end function;
	
	node_curves := [* *]; // pairs (h, Y_H) of node and corresponding curve
	
	// Constructs the fiber product curve Y_{J,K}
	FiberProduct := function(j,k)
		qJ := DefiningPolynomial(Y(Group(j)));
		qK := DefiningPolynomial(Y(Group(k)));
		A3<t,x,z> := AffineSpace(Rationals(),3);
		return Curve(Scheme(A3,[Evaluate(qJ,[t,x]),Evaluate(qK,[t,z])]));
	end function;
  
  // The procedure applied at every node during traversal of Sub(G)
  GetNodeData := procedure(node,~nodes_finite,~nodes_infinite,~node_pairs_finite,~known_groups,~node_curves)
		h := node; H := Group(h);
		"Computing node curve";
		YH,qH := Y(H);
		Append(~node_curves,<h,YH>);
		deltaH := {r[1]: r in Roots(Discriminant(qH))};
		for c in deltaH diff exceptional_set do
			Gc := GaloisGroup(Specialize(theta,c));
			Append(~known_groups, <c,Gc>);
		end for;
		
		curve_handled := false;
		for pair in nodes_finite do
			j := pair[1];
			if h le j then
				piH := {};
				for c in exceptional_set join deltaH join pair[2] do
					if HasRoot(Specialize(qH,c)) then Include(~piH,c); end if;
				end for;
				Append(~nodes_finite,<h,piH join deltaH>);
				curve_handled := true;
				"Points determined by finite node";
				break pair;
			end if;
		end for;
		
		if not curve_handled then
			for tup in node_pairs_finite do
				j := tup[1]; k := tup[2];
				if h lt j and h lt k then
					piH := {pt[1]: pt in tup[3] | HasRoot(Specialize(qH,pt[1]))};
					Append(~nodes_finite,<h,piH join deltaH>);
					curve_handled := true;
					"Points determined by node pair";
					break tup;
				end if;	
			end for;
		end if;
		
		if not curve_handled then
			AA := AffineSpace(Rationals(),2);
			for p:= 1 to #nodes_infinite do
				jnode := nodes_infinite[p];
				j := jnode[1];
				for q := p + 1 to #nodes_infinite do
					knode := nodes_infinite[q];
					 k := knode[1];
					if h lt j and h lt k then
						fp := FiberProduct(j,k);
						if IsIrreducible(fp) and Genus(fp) ne 1 then
								"Computing fiber product points";
								FF := FunctionField(fp);
								AF := MonicModel(AlgorithmicFunctionField(FF));
								AF := RationalExtensionRepresentation(AF);
								qJK := DefiningPolynomial(AF);
								assert {Denominator(co): co in Coefficients(qJK)} eq {1};
								poly := Polynomial([Evaluate(Numerator(co), AA.1) : co in Coefficients(qJK)]);
								f := Evaluate(poly, AA.2);
								gotpoints, m := RationalPoints_irreducible(Curve(AA,f),search_bound: genus0bound:=g0bound);
								if gotpoints and Type(m) eq SetIndx then
									"Fiber product proved finite";
									projections := {i[1]: i in m};
									piH := {};
									for c in projections do
										if HasRoot(Specialize(qH,c)) then Include(~piH,c); end if;
									end for;
									Append(~nodes_finite,<h,piH join deltaH>);
									Append(~node_pairs_finite,<j,k,m>);
									curve_handled := true;
									break p;
								end if;
								if gotpoints and Type(m) ne SetIndx then
									"Fiber product proved infinite";
								end if;
								if not gotpoints then
									"Fiber product undetermined";
								end if;
						end if;
					end if;
				end for;
			end for;
		end if;
		
		if not curve_handled then
			"Computing points on node curve";
			gotpoints, m := RationalPoints_irreducible(YH,search_bound: genus0bound:=g0bound);
			if gotpoints then
				if Type(m) eq SetIndx then
					piH := {i[1]: i in m};
					Append(~nodes_finite,<h,piH join deltaH>);
				else
					Append(~nodes_infinite,<h,m>);
				end if;
			else
				"Rational points undetermined";
			end if;
		end if;
	end procedure;
	
  // Compute the groups G_c for c up to height 10
  "\nComputing small height specializations";
  for c in {c: c in SmallHeightRationals(10)} join {c: c in wit} do
		if c notin exceptional_set then
			Gc := GaloisGroup(Specialize(theta,c));
			Append(~known_groups, <c,Gc>);
		end if;
  end for;
  top_realized := exists{i:i in known_groups|Order(i[2]) eq Order(G)};
	assert top_realized;
	"Top node realized";
  	
	// Breadth-first traversal of the poset Sub(G)
	"\nInitiating curve data gathering";
	visited := [Gsubs ! G];
	queue := [* <Gsubs ! G,0> *];
	while #queue ne 0 do
		h := queue[1][1]; depth := queue[1][2];
		if h in skip then
			"\nSkipping node", h;
		elif depth ne 0 then
			"\nVisiting node", h;
			"Node depth:", depth;
			GetNodeData(h,~nodes_finite,~nodes_infinite,~node_pairs_finite,~known_groups,~node_curves);
		end if;
		Remove(~queue,1);
		for m in MaximalSubgroups(h) do
			if m notin visited then
				Append(~visited,m);
				Append(~queue,<m,depth+1>);
			end if;
		end for;
	end while;
	"\nCurve data gathering completed";
	
	/* Generate rational points on curves and
	compute corresponding Galois groups */
	"\nRealizing groups using curve data";
	counter := 0;
	for pair in nodes_finite do
		for c in pair[2] diff exceptional_set do
			Gc := GaloisGroup(Specialize(theta,c));
			counter +:= 1;
			Append(~known_groups, <c,Gc>);
		end for;
	end for;
	counter, "groups realized via finite nodes";
	counter := 0;
	for pair in nodes_infinite do
		m := pair[2]; // m is a map describing a curve Y_H
		crv := Domain(m);
		if Genus(crv) eq 0 then // m maps P^1 to Y_H
			pointset := {m(crv ! [r,1]): r in SmallHeightRationals(10)};
			cset := {pt[1]/pt[3] : pt in pointset | pt[3] ne 0};
			for c in cset diff exceptional_set do
				Gc := GaloisGroup(Specialize(theta,c));
				counter +:= 1;
				Append(~known_groups, <c,Gc>);
			end for;
		else // m maps Y_H to elliptic curve
			elliptic := Codomain(m);
			pointset := {@ @};
			for i in Points(elliptic: Bound:=500) do
				pointset join:= Points(Pullback(m,i));
			end for;
			cset := {pt[1]/pt[3] : pt in pointset | pt[3] ne 0};
			for c in cset diff exceptional_set do
				Gc := GaloisGroup(Specialize(theta,c));
				counter +:= 1;
				Append(~known_groups, <c,Gc>);
			end for;
		end if; 
	end for;
	counter, "groups realized via infinite nodes";
	
	// Gather the nodes into equivalence classes
	"\nBuilding node equivalence classes";
	node_classes := [* *];
	for h in Gsubs do
		H := Group(h);
		is_represented := exists(hclass){i:i in node_classes|IsConjugate(SM,H,Group(i[1]))};
		if is_represented then
			Remove(~node_classes,Index(node_classes,hclass));
			Append(~node_classes,Append(hclass,h));
		else
			Append(~node_classes,[* h *]);
		end if;
	end for;
	"Total of", #node_classes, "equivalence classes";
	
	/* Checks whether a given equivalence class of nodes
	is strongly realizable using data from nodes_finite */
	IsStronglyRealizable := function(class)
		if #class eq 1 and class[1] eq Gsubs ! G then return true; end if;
		if forall{d : d in class | exists{i: i in nodes_finite| d eq i[1]}} then
			for d in class do
			trash := exists(pair){i: i in nodes_finite| d eq i[1]};
			assert trash;
			D := Group(d);
			cset := pair[2] diff exceptional_set;
			if exists{c: c in cset | IsConjugate(SM,GaloisGroup(Specialize(theta,c)),D)} then
				return true;
			end if;
			end for;
		end if;
		return false;
	end function;
	
	"\nFinding unrealizable nodes";
	unrealizable := {@ @}; // nodes proved not to be strongly realizable
	
	for class in node_classes do
		if not IsStronglyRealizable(class) then
			for d in class do Include(~unrealizable,d); end for;
		end if;
	end for;
	#unrealizable, "nodes proved unrealizable";
	
	"\nFinal classification of nodes";
	realized := [* *]; // nodes realized in the form G_c for some rational c
	unknown := [* *]; // nodes whose realizability in the form G_c is unknown
	
	for h in Gsubs do
		"\nClassifying node", h;
		H := Group(h);
		if h in skip then
			"Node was skipped";
			if exists{i:i in known_groups|IsConjugate(SM,H,i[2])} then
				"Node is realized";
			else
				"Node is unknown";				
				Append(~unknown,H);
			end if;
		else
			if h in unrealizable then
				"Node is unrealizable";
			else
				is_realized := exists(pair){i:i in known_groups|IsConjugate(SM,H,i[2])};
				if is_realized then
					c := pair[1];
					"Node is realized by", c;
					Append(~realized, <c,H>);
				else
					"Node not realized"; 
					"Attempting to realize";
					trash := exists(pair){i: i in node_curves | h eq i[1]};
					assert trash;
					YH := pair[2];
					cset := {pt[1] : pt in CurveSearch(YH,1,30)} diff exceptional_set;
					is_realized := exists(c){s: s in cset | IsConjugate(SM,H,GaloisGroup(Specialize(theta,s)))};
					if is_realized then
						"Node realized by", c;
						Append(~realized, <c,H>);
					else
						cset := {pt[1] : pt in CurveSearch(YH,10^3,50)} diff exceptional_set;
						is_realized := exists(c){s: s in cset | IsConjugate(SM,H,GaloisGroup(Specialize(theta,s)))};
						if is_realized then
							"Node realized by", c;
							Append(~realized, <c,H>);
						else
							"Node is unknown";
							Append(~unknown,H);
						end if;
					end if;
				end if;
			end if;
		end if;
	end for;
	
	// Collect representatives of the realized and unknown nodes.
	group_set := {i[2]: i in realized} join {i: i in unknown};
	groups_inequivalent := [* *];
	for H in group_set do
		if not exists{i: i in groups_inequivalent|IsConjugate(SM,H,i)} then
			Append(~groups_inequivalent,H);
		end if;
	end for;
	"\nEnded with", #unknown, "unknown nodes";
	return exceptional_set,groups_inequivalent,realized,unknown;
end function;

// A simplified version of GSAp meant for easier examples
GSA := function(poly)
	"\nComputing generic Galois group";
	G,_,galois_data := GaloisGroup(poly);
	"Computing poset of subgroups";
	Gsubs := SubgroupLattice(G);
	e,g,_,_ := GSAp(poly,G,galois_data,Gsubs);
	return e,g;
end function;

// Additional functionality for computing factorization types and densities
SpecializationData := function(groups)
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
	return factorization_types, densities;
end function;
