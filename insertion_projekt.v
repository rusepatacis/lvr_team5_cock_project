Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import BauerSorting.

Open Scope Z_scope.

(** 
   Pomozna funckija za vstavljanje celega stevila x v seznam celih stevil l.
**)
Fixpoint insert (x: Z) (l: list Z): list Z :=
   match l with
      | nil => x :: nil   (* Robni primer - stakni glavo (x) z praznim seznamom, x je torej trenutno najmanjsi element, ki smo ga obdelali *)
      | (cons y l') =>  (* Seznam, staknjen iz glave y in repa l' *)
           if (Z_le_gt_dec x y) then 
              (** Element x je manjsi ali enak od trenutne glave y, vstavi x * *)
              (x :: l)
           else 
              (** Element x je vecji od trenutne glave y,
               poklici rekurzijo, potuj po seznamu, dokler ne prides do manjsega elementa **)
              (y :: (insert x l'))      
      end.

(** 
   Glavna funkcija insertion_sort  za cela stevila
**)
Fixpoint insertion_sort (l: list Z): list Z :=
   match l with
      | nil => nil (* Prazen seznam je urejen *)
      | (cons x l') => insert x (insertion_sort l') (* Potuj po seznamu, premikaj trenutno glavo na ustrezno mesto *)
   end.

(* Pomozna lema, uporabljena v dokazu ohranjanje_urejenosti_vstaljanja *)
Lemma manjse_enako (a: Z) (b: Z): a < b -> a <= b.
Proof.
  intro.
  case (Z_le_gt_dec a b).
  - intro.
    assumption.
  - intro.
    firstorder.
Qed.

Hint Resolve urejen_tail urejen_head urejen_lt_cons najmanjsi_inv najmanjsi_In najmanjsi_head najmanjsi_tail : urejen_hint.

Lemma ohranjanje_urejenosti_vstavljanja (x: Z) (l: list Z): urejen l -> urejen(insert x l).
Proof.
   intro. (* Vpeljava *)
   induction l. (* Dokaz z indukcijo po senznamu l *)
   - auto. (* Vstavljanje v prazen seznam *)
   - simpl. (* Netrivialen primer *)
     case (Z_le_gt_dec x a). (* Primerjamo element, ki ga vstavljamo, s trenutno glavo *)
     * simpl. (* Primer x <= a: samo staknemo x na zacetku, seznam je urejen *)
       auto.
     * intro. (* Primer x > a: potujemo po seznamu in x vstavimo na ustrezno mesto. *)
       simpl.
       destruct l. (* Locimo primere glede na seznam *)
       + simpl. (* Prazen seznam *)
         split.
            apply manjse_enako.
            firstorder.

            assumption. (* Vedno predpostavimo resnico *)
       + simpl. (* Seznam sestavljen iz glave in repa *)
         case (Z_le_gt_dec x z). (* Locimo primere glede na primerjavo z glavo *)
           simpl. (* x <= z ; razpise definicijo urejen*)
           intros. (* Dokazujemo implikacijo *)
           split. (* Dokaz konjunkcije *)
             firstorder. (* Telovadba z neenakostmi *)
             
             split. (* Dokaz konjunkcije *)
              assumption.
              firstorder.
           
           split. (* x > z *)
              firstorder. (* Telovadba z neenakostmi *)
           
              replace (z :: insert x l) with (insert x (z :: l)). (* Ker zelimo uporabiti hipotezo IHl (njen desni del *)
              apply urejen_tail in H. (* Poenostavimo H, da ustreza levemu delu IHl in s tem pridobimo 'desni del' IHl *)
              firstorder.  (* Ocitno iz implikacije v hipotezah *)
              simpl. (* Razpis insert *)
              firstorder. (* Poenostavimo kar se da v hipotezah *)
              destruct (Z_le_gt_dec x z). (* V hipotezah imamo ustrezen pogoj, moti nas notacija Z_le_gt_dec, zelimo > <= *)
              firstorder.
              firstorder.
Qed.



(* pomozna lema za dokazovanje, da je sortiran seznam enak neurejenemu seznamu,
 tukaj gledamo primer ko x != y * *)
Lemma ni_enak (x y : Z) (l : list Z): (x =? y = false) -> pojavi x l = pojavi x (insert y l).
Proof.
   intro.
   induction l. (* indukcija po seznamu *)
   -simpl. (* privzeli smo da x != y *)
    rewrite H. (* leva stran je enaka desni *)
    auto.
   -simpl. (* lociti moramo po x=a in y < a *)
    case (Z_le_gt_dec y a).
    +intro. (* y <= a *)
     case_eq (x =? a). (* x = a *)
     *intro. (* x = a *)
      simpl. (* velja x = a in x != y *)
      rewrite H.
      rewrite H0. (* leva stran = desni strani *)
      auto.
     *intro. (* x != a *)
      simpl. (* velja x != y in x != a *)
      rewrite H.
      rewrite H0. (* leva stran enaka desni *)
      auto.
    +intro. (* y > a *)
     case_eq (x =? a).
     *intro. (* x = a *)
      simpl. (* velja x =a *)
      rewrite H0. (* notranja leva stran je ravno leva stran IHl *)
      rewrite IHl. (* leva stran je enaka desni *)
      auto.
     *intro. (* x != a *)
      simpl. (* velja x != a *)
      rewrite H0. (* ocitno je enako *)
      auto.
Qed.


(* pomozna lema, gledamo primer ko je x = y *)
Lemma enak(x y : Z) (l : list Z): (x =? y = true ) -> pojavi x (insert x l) = S (pojavi x l).
Proof.
   intro.
   induction l. (*indukcija po seznamu *)
   -simpl. (* if x = x -> vedno true *)
    rewrite Z.eqb_refl.
    auto. (* ocitno *)
   -simpl. (* locimo glede na x > a in x = a *)
    case (Z_le_gt_dec x a). (* x <= a *)
    +intro. (* <= *)
     case_eq (x =? a). (* x = a *)
     *intro.
      simpl. (* velja x = a in ocitno x=x *)
      rewrite H0.
      rewrite Z.eqb_refl. (* ocitno je leva stran enaka desni *)
      auto.
     *intro. (* x != a *)
      simpl. (* velja x != a in x = x *)
      rewrite H0.
      rewrite Z.eqb_refl. (* ocitno je leva stran enaka desni *)
      auto.
    +intro. (* x > a *)
     case_eq (x =? a).
     *intro. (* x = a *)
      simpl. (* velja x = a *)
      rewrite H0. (* notranja leva stran je ravno IHl leva stran IHl *)
      rewrite IHl. (*leva stran = desni strani *)
      auto.
     *intro. (* x != a *)
      simpl. (* velja x != a *)
      rewrite H0. (* ponovno je leva stran enaka IHl *)
      rewrite IHl.
      auto. 
Qed. 


(* ::: Dokaz pravilnosti ::: *)
(* Rezulat insterition sorta je urejen seznam, ki je obenem permutacija vhodnega seznama *)
Theorem insertion_sort_deluje: forall lst: list Z, urejen (insertion_sort lst)  /\ permutiran lst (insertion_sort lst).
Proof.
   intro.
   split. (* Dokazemo oba dela izreka *)
   - induction lst. (* Prvi del izreka ... UREJENOST *)
      * reflexivity. (* Trivialen primer *)
      * apply ohranjanje_urejenosti_vstavljanja. (* Tu uporabi pomozno lemo *)
        auto.
   -  intro. (* Drugi del izreka ... JE PERMUTACIJA *)
      induction lst. (* indukcija po seznamu *)
      * reflexivity. (* trivialen primer *)
      * simpl.      (* potrebno lociti glede na x = a *)
        case_eq (x =? a).
           + intro.     (* x = a *)
             rewrite Z.eqb_sym in H. (* obrnemo ter uporabimo hipotezo H, *)
             rewrite Z.eqb_eq in H.  (* da se znebimo a iz cilja *)
             rewrite H.
	     rewrite (enak x a). (* uporabimo pomozno lemo *)
	     auto.
             rewrite H.
	     rewrite Z.eqb_refl.
	     auto.
	   + intro.   (* x != a *)
             rewrite IHlst. (* razpisemo cilj *)
	     rewrite (ni_enak x a). (* uporabimo pomozno lemo *)
	     auto. (* ocitno *)
	     auto. (* H *)
Qed.
  

