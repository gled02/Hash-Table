module type HashStringToInt =
	sig
		type hashStringToInt
		val mapVide : hashStringToInt
		val estDans : hashStringToInt * string -> bool
		val insertion : hashStringToInt * string -> hashStringToInt
		val suppression : hashStringToInt * string -> hashStringToInt
		val union : hashStringToInt -> hashStringToInt -> hashStringToInt
		val intersection : hashStringToInt -> hashStringToInt -> hashStringToInt
		val difference : hashStringToInt -> hashStringToInt -> hashStringToInt
		val differenceSym : hashStringToInt -> hashStringToInt -> hashStringToInt
		val appliquer_sur : (valeur -> valeur -> valeur) -> hashStringToInt -> valeur -> valeur
	end
	
module MakeTableHash : HashStringToInt =
	struct
		type couleur = Rouge | Noir | DoubleNoir
  	type 'a arbre = Vide | VideNoir | Noeud of ('a * couleur * 'a arbre * 'a arbre)
		type valeur = string
		type hashStringToInt = (int * valeur arbre) arbre
  	
		let clef_comp = (-)
		let val_comp = String.compare
		let hash = String.length

 		let mapVide = Vide
		
		let rec estDansArbreMot (a,s) =
  		match a with
  			| Vide | VideNoir -> false
  			| Noeud(x,_,_,_) when (val_comp x s) = 0 -> true
  			| Noeud(x,_,_,d) when (val_comp x s) < 0 -> estDansArbreMot (d,s)
  			| Noeud(x,_,g,_) -> estDansArbreMot (g,s);;
  
  	let rec estDans (a,s) =
  		match a with
  			| Vide | VideNoir -> false
  			| Noeud(x,_,_,_) when (clef_comp (fst x) (hash s)) = 0 && estDansArbreMot ((snd x),s) -> true
  			| Noeud(x,_,_,_) when (clef_comp (fst x) (hash s)) = 0 && not(estDansArbreMot ((snd x),s)) -> false
  			| Noeud(x,_,_,d) when (clef_comp (fst x) (hash s)) < 0 -> estDans (d,s)
  			| Noeud(x,_,g,_) -> estDans (g,s);;

  	let estVide = function
  		| Vide | VideNoir -> true
    	| _-> false;;
  
  	let racineRouge = function
  		| Noeud(_,Rouge,_,_) -> true
  		| _-> false;;
  
 		let aUnFilsRouge = function
  		| Noeud(_,_,g,d) -> racineRouge g || racineRouge d
  		| _-> false;;
  
  	let coloreRacine c = function
  		| Noeud(e,_,ag,ad)-> Noeud(e,c,ag,ad)
  		| a -> a;;
  
    let rotationGauche = function
  		| Noeud(m,cm,a1,Noeud(n,cn,a2,a3))-> Noeud(n,cn,Noeud(m,cm,a1,a2),a3)
  		| _-> failwith "pas de rotation gauche";;
  
  	let rotationDroite = function
  		| Noeud(n,cn,Noeud(m,cm,a1,a2),a3) -> Noeud(m,cm,a1,Noeud(n,cn,a2,a3))
  		| _-> failwith "pas de rotation droite";;
  
  	let rec equilibrer = function
  	  | Noeud(e,Noir,(Noeud(_,Rouge,_,_) as ag),(Noeud(_,Rouge,_,_) as ad)) 
			  when aUnFilsRouge ag || aUnFilsRouge ad 
				  -> Noeud(e,Rouge,coloreRacine Noir ag,coloreRacine Noir ad)
  		| Noeud(g,Noir,(Noeud(_,Rouge,Noeud(_,Rouge,_,_),_) as p),f) 
			    -> rotationDroite (Noeud(g,Rouge,coloreRacine Noir p,f))
  		| Noeud(g,Noir,(Noeud(_,Rouge,_,Noeud(_,Rouge,_,_)) as p),f) 
			    -> equilibrer (Noeud(g,Noir,rotationGauche p,f))
  		| Noeud(g,Noir,f,(Noeud(_,Rouge,Noeud(_,Rouge,_,_),_)as p)) 
		    	-> equilibrer (Noeud(g,Noir,f,rotationDroite p))
  		| Noeud(g,Noir,f,(Noeud(_,Rouge,_,Noeud(_,Rouge,_,_))as p)) 
			    -> rotationGauche (Noeud(g,Rouge,f,coloreRacine Noir p))
 			| a -> a;;
  
  	let insererArbreMot v a =
  	 	let rec aux = function
  			| Vide | VideNoir -> Noeud(v,Rouge,Vide,Vide)
  			| Noeud(e,_,_,_) as ab when (val_comp e v) = 0 -> ab
  			| Noeud(e,c,ag,ad) when (val_comp e v) > 0 -> equilibrer (Noeud(e,c,aux ag,ad))
  			| Noeud(e,c,ag,ad)-> equilibrer (Noeud(e,c,ag,aux ad))
  	 	in coloreRacine Noir (aux a);;
  
    let insertion (a,v) =
  		let rec aux = function
				| Vide | VideNoir
						-> Noeud(((hash v), Noeud(v, Noir, Vide, Vide)),Rouge,Vide,Vide)
				| Noeud(e,c,ag,ad) as ab when estDans(ab,v)
						-> ab
				| Noeud(e,c,ag,ad) as ab when not(estDans (ab,v)) && (clef_comp (hash v) (fst e)) = 0
						-> equilibrer (Noeud(((fst e),insererArbreMot v (snd e)),c,ag,ad))
				| Noeud(e,c,ag,ad) when (clef_comp (hash v) (fst e)) < 0
						-> equilibrer (Noeud(e,c,aux ag,ad))
				| Noeud(e,c,ag,ad)
						-> equilibrer (Noeud(e,c,ag,aux ad))
			in coloreRacine Noir (aux a);;
		
		(*Suppression -------------------------------------------- *)

	  let probleme = function
			| VideNoir | Noeud(_,DoubleNoir,_,_) -> true
			| _-> false;;

		let cas1 = function
			| Noeud(_,Noir,(Vide|Noeud(_,Noir,_,_)),(Vide|Noeud(_,Noir,_,_))) -> true
			| _-> false;;

		let augmenter = function
  		| Rouge -> Noir
			| Noir -> DoubleNoir
			| _-> failwith "Augmentation impossible";;

		let diminuerCouleur = function
			| VideNoir -> Vide
			| Noeud(r,Noir,g,d) -> Noeud(r,Rouge,g,d)
			| Noeud(r,DoubleNoir,g,d) -> Noeud(r,Noir,g,d)
			| _-> failwith "Impossible de diminuer";;

		let appEquilibrageSousAbGauche f = function
			| Vide| VideNoir -> failwith "Pas de Noeud"
			| Noeud(a,c,ag,ad) -> Noeud(a,c,f ag,ad);;

		let appEquilibrageSousAbDroit f = function
			| Vide| VideNoir -> failwith "Pas de Noeud"
			| Noeud(a,c,ag,ad) -> Noeud(a,c,ag,f ad);;

		let rec equilibrerSupp = function
			| Noeud(vp,cp,x,f) when probleme x && cas1 f || cas1 x && probleme f
					-> Noeud(vp,augmenter cp,diminuerCouleur x,diminuerCouleur f)
			| Noeud(p,c,x,Noeud(f,Noir,agf,Noeud(d,Rouge,agd,add))) when probleme x
					-> rotationGauche (Noeud(p,Noir,diminuerCouleur x,Noeud(f,c,agf,Noeud(d,Noir,agd,add))))
			| Noeud(p,c,x,Noeud(f,Noir,Noeud(g,Rouge,agg,adg),d)) when probleme x
					-> equilibrerSupp (Noeud(p,c,x,rotationDroite (Noeud(f,Rouge,Noeud(g,Noir,agg,adg),d))))
			| Noeud(p,c,x,Noeud(f,Rouge,agf,adf)) when probleme x
					-> appEquilibrageSousAbGauche equilibrerSupp (rotationGauche (Noeud(p,Rouge,x,Noeud(f,Noir,agf,adf))))
			| Noeud(p,c,Noeud(f,Noir,Noeud(g,Rouge,agg,adg),adf),x) when probleme x
					-> rotationDroite (Noeud(p,Noir,Noeud(f,c,Noeud(g,Noir,agg,adg),adf),diminuerCouleur x))
			| Noeud(p,c,Noeud(f,Noir,g,Noeud(d,Rouge,agd,add)),x) when probleme x
					-> equilibrerSupp (Noeud(p,c,rotationGauche (Noeud(f,Rouge,g,Noeud(d,Noir,agd,add))),x))
			| Noeud(p,c,Noeud(f,Rouge,agf,adf),x) when probleme x
					-> appEquilibrageSousAbDroit equilibrerSupp (rotationDroite (Noeud(p,Rouge,Noeud(f,Noir,agf,adf),x)))
			| a -> a;;

		let rec supprimerMaxArbreMot = function
			| Vide | VideNoir -> failwith "Pas de max"
			| Noeud(r,Rouge,Vide,Vide) -> (r,Vide)
			| Noeud(r,Noir,Noeud(y,Rouge,Vide,Vide),Vide) -> (r,Noeud(y,Noir,Vide,Vide))
			| Noeud(r,Noir,Vide,Vide) -> (r,VideNoir)
			| Noeud(_,_,_,Vide)-> failwith "Pas bicolor"
			| Noeud(r,c,g,d) -> let (m, d2) = (supprimerMaxArbreMot d) in (m,equilibrerSupp (Noeud(r,c,g,d2)));;

		let rec supprimerMaxHash = function
			| Vide | VideNoir -> failwith "Pas de max"
			| Noeud((n,r),Rouge,Vide,Vide) -> ((n,r),Vide)
			| Noeud((n,r),Noir,Noeud(y,Rouge,Vide,Vide),Vide) -> ((n,r),Noeud(y,Noir,Vide,Vide))
			| Noeud((n,r),Noir,Vide,Vide) -> ((n,r),VideNoir)
			| Noeud(_,_,_,Vide)-> failwith "Pas bicolor"
			| Noeud((n,r),c,g,d) -> let (m, d2) = (supprimerMaxHash d) in (m,equilibrerSupp (Noeud((n,r),c,g,d2)));;

		let stabiliser = function
			| VideNoir -> Vide
			| Noeud(r,DoubleNoir,g,d) -> Noeud(r,Noir,g,d)
			| a -> a;;

		let supprimerArbreMot x a =
			let rec aux = function
				| Vide -> Vide
				| VideNoir -> VideNoir
				| Noeud(v,c,g,d) when (val_comp x v) < 0 -> equilibrerSupp (Noeud(v,c,aux g,d))
				| Noeud(v,c,g,d) when (val_comp x v) > 0 -> equilibrerSupp (Noeud(v,c,g,aux d))
				| Noeud(v,Rouge,Vide,Vide) -> Vide
				| Noeud(v,Noir,Vide,Vide) -> VideNoir
				| Noeud(v,Noir,Vide,Noeud(y,Rouge,Vide,Vide)) -> Noeud(y,Noir,Vide,Vide)
				| Noeud(v,c,g,d) -> let (m,g2) =  supprimerMaxArbreMot g in equilibrerSupp (Noeud(m,c,g2,d))
			in stabiliser (aux a);;

		let suppression (a,x) =
			let rec aux = function
				| Vide -> Vide
				| VideNoir -> VideNoir
				| Noeud((n,s),_,_,_) when estVide s -> VideNoir
				| Noeud((n,s),c,g,d) when (clef_comp (hash x) n) < 0 -> equilibrerSupp (Noeud((n,s),c,stabiliser (aux g),d))
				| Noeud((n,s),c,g,d) when (clef_comp (hash x) n) > 0-> equilibrerSupp (Noeud((n,s),c,g,stabiliser (aux d)))
				| Noeud((n,s),c,Vide,Vide) as ab when estDans (ab,x) -> aux (Noeud((n,(supprimerArbreMot x s)),c,Vide,Vide))
				| Noeud((n,s),Noir,Vide,Noeud(y,Rouge,Vide,Vide)) as ab when estDans (ab,x) -> equilibrerSupp (Noeud((n,(supprimerArbreMot x s)),Noir,Vide,Noeud(y,Noir,Vide,Vide)))
				| Noeud((n,Noeud(_,_,Vide,Vide)),c,g,d) as ab when estDans (ab,x)
						-> let (m,g2) = supprimerMaxHash g in equilibrerSupp (Noeud(m,c,g2,d))
				| Noeud((n,s),c,g,d)
						-> equilibrerSupp (Noeud((n,(supprimerArbreMot x s)),c,g,d))
			in stabiliser (aux a);;

    (*Union, Intersection, Différence ensembliste et *)
		(* symétrique, op. d'accumulation ------------------------ *)
		
 		let exploser = function
			| Vide | VideNoir -> failwith "Vide"
			| Noeud(v,_,ag,ad) -> (v,coloreRacine Noir ag,coloreRacine Noir ad);;

		let union a b =
			let rec aux acc = function
				| [] -> acc
				| Vide::asl -> aux acc asl
				| a'::asl -> let ((n,r),ag,ad) = exploser a' in
				            	 let (s,ag',ad') = exploser r in 
												aux (insertion (acc,s)) (ag::ad::asl)
			in aux a [b];;

    let intersection a b = 
			let rec aux acc = function
				| [] -> acc
				| Vide::asl -> aux acc asl
				| a'::asl -> let ((n,r),g,d) = exploser a' in 
											let (s,ag,ad) = exploser r in
												if estDans (a,s) then
													aux (insertion (acc,s)) (g::d::asl)
												else
											  	aux acc (g::d::asl)
			in aux Vide [b];;

		let difference a b =
			let rec aux acc = function
				| [] -> acc
				| Vide::asl -> aux acc asl
				| a'::asl -> let ((n,r),g,d) = exploser a' in 
											let (s,ag,ad) = exploser r in
											 if not(estDans (b,s)) then
													aux (insertion (acc,s)) (g::d::asl)
											 else
											 		aux acc (g::d::asl)
			in aux Vide [a];;

		let differenceSym a b = union (difference a b) (difference b a);;

		let rec appliquer_sur f a acc = 
			match a with
				| Vide -> acc
				| _-> let ((n,r),ag,ad) = exploser a in
				      	let (s,ag',ad') = exploser r in
				      		appliquer_sur f ag (f s (appliquer_sur f ad acc));;

	end

module EnsHash = MakeTableHash;;
open EnsHash;;

let a = insertion(insertion(insertion(insertion(insertion(insertion(insertion(mapVide,"table"),"de"),"hasahge"),"donnees"),"strucutre"),"tableau"),"associatif");;
let b = insertion(insertion(insertion(mapVide,"table"),"de"),"abcde");;

suppression (a,"tableau");;
union a b;;
intersection a b;;
difference a b;;
differenceSym a b;;
