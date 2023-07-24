
import base
import .generique
import .cardinalite_finie
open generique

namespace groupe
open groupe
/- 
Structure d'un sous_groupe : 
pour un groupe G, on fournit un sous ensemble et les preuves de stabilité de G.mul et G.inv
-/
structure sous_groupe (G: groupe) :=
  (sous_ens : set G)
  (mul_stab : ∀ a b ∈ sous_ens, a * b ∈ sous_ens)
  (inv_stab : ∀ a ∈ sous_ens, a⁻¹ ∈ sous_ens)
  (contient_neutre : (1:G) ∈ sous_ens )


/-
Coercion permettant de voir un sous groupe d'un groupe G comme étant lui même
un groupe. 
Il suffit de fournir les éléments de la structure de groupe:
  * .ens sera le sous-type de G.ens qui correspond à l'ensemble du ss-groupe 
  * .mul et .inv seront juste la 'restriction' au sous type (en utilisant la preuve de stabilité)
  * .neutre sera le neutre de G
  * On fournit les preuves de l'associativité, l'inversibilité et neutre à gauche
  * Commentaires pour décrire la preuve incomming
-/
instance sous_groupe_to_groupe {G: groupe}:
  has_coe (sous_groupe G) groupe :=
  ⟨λ SG : sous_groupe G,
  {groupe .
    ens := {a // a ∈ SG.sous_ens},
    mul :=  λ x y, ⟨x.val*y.val, SG.mul_stab x.val x.property y.val y.property⟩,
    inv := λ x, ⟨x.val⁻¹, SG.inv_stab x.val x.property⟩,
    neutre := ⟨G.neutre, SG.contient_neutre⟩,
    mul_assoc := λ x y z, by {rw subtype.mk.inj_eq, unfold subtype.val, exact G.mul_assoc x y z},
    neutre_gauche := λ x, by {cases x, rw subtype.mk.inj_eq, unfold subtype.val, exact G.neutre_gauche _},
    inv_gauche := λ x, by {rw subtype.mk.inj_eq, unfold subtype.val, exact G.inv_gauche x.val},
  }⟩

/-
Coercion permettant d'écrire (x : H) avec H un sous_groupe, et voir x comme un élément du type des éléments.
Normalement, on a déjà une coercion qui avec (G: groupe) et (H: sous_groupe G) nous fait :
H -> A:groupe -> A.ens (avec A.ens égal à {a:G.ens//a∈H.sous_ens}) -> G.ens
Mais la dernière coercion ne se fait pas (https://proofassistants.stackexchange.com/q/2014/2164) 
-/
instance sous_groupe_to_sous_type {G: groupe} 
  : has_coe_to_sort (sous_groupe G) (Type) :=
  ⟨λ H, {a // a ∈ H.sous_ens}⟩ 


-- ↓Coertions utile quand on veut voir un sous groupe comme un ensemble (ex: déf de distingué)
instance sous_groupe_to_sous_ens {G: groupe} 
  : has_coe (sous_groupe G) (set G) :=
  ⟨λ H, H.sous_ens⟩ 
instance appartient_sous_groupe {G: groupe} 
  : has_mem G (sous_groupe G) :=
  ⟨λ x H, H.sous_ens x⟩ 



/-
↓ ↓ ↓ Différents lemmes permettant de faire le lien entre les éléments et opérations dans un groupe et un sous groupe ↓ ↓ ↓ 
-/
lemma eq_in_ss_groupe_iff_eq {G : groupe} {H : sous_groupe G} (a b : H)
  : ((a:G) = ↑b) ↔ (a = b) :=
begin
  split; intro p; try {rw p},
  unfold coe at p, unfold lift_t at p, unfold has_lift_t.lift at p,
  unfold coe_t at p, unfold has_coe_t.coe at p, unfold coe_b at p,
  unfold has_coe.coe at p, apply subtype.eq, exact p,
end

lemma mem_ss_groupe_simp {G : groupe} {H : sous_groupe G}
  : ∀ a, (a ∈ H) ↔ (a ∈ (H : set G)) 
  := by {intro, split;intro p; unfold has_mem.mem at *; unfold coe at *; unfold lift_t at *;
        unfold has_lift_t.lift at *;  unfold coe_t at *; unfold has_coe_t.coe at *;
        unfold coe_b at *; unfold has_coe.coe at *; exact p,}

lemma coe_mul_sous_groupe {G : groupe} {H : sous_groupe G} (a b : (H : groupe))
  : (a*b).val = a.val*b.val := rfl
lemma coe_sous_groupe {G : groupe} {H : sous_groupe G} (a : H) 
  :  (a : G) =  a.val := rfl
lemma coe_sous_groupe₂ {G : groupe} {H : sous_groupe G} (a : G) (a_H : a∈H)
  : a = ((⟨a, a_H⟩:H) : G) := rfl
lemma coe_one_sous_groupe {G : groupe} {H : sous_groupe G}
  : (1 : (H:groupe)).val = (1 : G) := rfl



-- Deux sous groupes d'un même groupe G sont égaux ssi leurs ensembles sont égaux
lemma sous_groupe_eq_iff {G : groupe} {H H': sous_groupe G}
  : H = H' ↔ (H:set G) = (H':set G) :=
begin
  split;intro p, rw p,
  unfold coe lift_t has_lift_t.lift coe_t has_coe_t.coe coe_b has_coe.coe at p,
  cases H, cases H', simp at p ⊢, rw p,
end 


/-***************************************Fin Définitions et coercions de base **************************************-/






/-**********************Diverses définitions pour gérer les sous groupes de sous groupes*************************** -/
/-
- Section permettant de travailler avec des chaines de sous groupes, dans la situation K < H < G
- Il y a deux possibilités ici : 
  - Donnés un groupe G, H : sous_groupe G et K : sous_groupe H, on voudrait voir K comme un sous_groupe G
    --> C'est fait avec une coercion qui associe à tout élément de sous_groupe H l'élément de sous_groupe G correspondant
    --> Pas besoin de notation dans ce cas, lean pourra faire la conversion selon le contexte
  - Données un groupe G, H et K deux sous_groupe G et une preuve que K est inclus dans H, voir K comme un sous_groupe H
    --> Pas possible de le faire avec une coercion de (sous_groupe G) vers (sous_groupe H) car c'est à condition que K⊆H
        (est-il possible d'avoir une coercion qui dépend d'une condition sur l'ensemble de départ ?)
- Il faut ensuite faire le lien entre ces deux opérations en montrant qu'elles sont inverses l'une de l'autre : 
  - Si on convertit un sous groupe de H vers un sous groupe de G, et qu'on reconvertit le résultat vers un sous groupe de H, on doit 
    revenir au même sous groupe de départ
  - Inversement, si on a H < G, K < G et K ⊆ H, en convertissant K vers un sous_groupe de H, puis en voyant le résultat de cette
    convertion comme un sous groupe de G, on doit avoir le même objet exactement que celui de départ.

- Notations introduites dans cette partie : 
  - K ⊆₁ H pour K et H deux sous_groupe G : veut dire que l'ensemble de K est inclus dans l'ensemble de H
    --> S'écrit grâce à \sub\1
    --> explication de pouquoi cette notation au lieu de ⊆ plus bas.
  - (K↘H) avec H et K deux sous_groupe G et K ⊆₁ H : veut dire K vu comme un sous_groupe H
    --> S'écrit grâce à \dr 
-/


-- Classe représentant une preuve que K.sous_ens ⊆ H.sous_ens. 
-- C'est une classe afin de permettre à lean de chercher une instance tout seul pour pouvoir convertir K en sous groupe de H
-- La notation ⊆ n'est pas utilisée car si on l'utilise (avec has_sub) lean ne devine plus que (H ⊆ K) est une instance de sous_groupe_incl 
class sous_groupe_incl {G : groupe} (H K : sous_groupe G) : Prop :=
  (h : (H:set G) ⊆ K)
notation H `⊆₁`:52 K := sous_groupe_incl H K


-- Convertion n°1 : On voit les sous_groupes de H comme des sous_groupes de G
instance sous_sous_groupe_to_sous_groupe {G : groupe} {H : sous_groupe G}
  : has_coe (sous_groupe H) (sous_groupe G) :=
  ⟨λ K, {
    sous_ens := {x | x∈H ∧ ∀ h : x∈H, (⟨x, h⟩: H)∈K},
    mul_stab := λa ha b hb, ⟨H.mul_stab _ ha.1 _ hb.1, λ h, K.mul_stab _ (ha.2 ha.1) _ (hb.2 hb.1)⟩, 
    inv_stab := λa ha, ⟨H.inv_stab _ ha.1, λ h, K.inv_stab _ (ha.2 ha.1)⟩,
    contient_neutre := ⟨H.contient_neutre, λ h, K.contient_neutre⟩
  }⟩

-- Convertion n°2 : On voit un sous groupe de G inclus dans H comme un sous groupe de H
def sous_groupe_to_sous_sous_groupe {G : groupe} (H : sous_groupe G) 
  (K: sous_groupe G) [p : K ⊆₁ H] : sous_groupe H := 
{
  sous_ens := {g | g.val ∈ K},
  mul_stab := λ a pa b pb, K.mul_stab _ pa _ pb,
  inv_stab := λ a pa, K.inv_stab _ pa,
  contient_neutre := K.contient_neutre, 
}
-- Notation pour la convertion n°2 : on écrit K↘H pour voir K comme sous groupe de H. ↘ est écrit avec \dr
notation K `↘`:65 H:65 := sous_groupe_to_sous_sous_groupe H K 
example (G : groupe) (H K : sous_groupe G) (KinH: (K ⊆₁ H)) := (K↘H)

-- lemme montrant la cohérence des deux conversions : 
-- un sous groupe de H vu comme un sous groupe de G, est inclus dans H
@[instance] lemma ss_gr_of_ss_ss_gr_sub {G : groupe} {H : sous_groupe G} (K : sous_groupe H) 
  : (K : sous_groupe G) ⊆₁ H := ⟨λ x px, px.1⟩



-- ↓ Description de l'ensemble du sous groupe de H obtenu à partir de K ⊆ H
lemma sous_groupe_down_ens {G : groupe} {H K: sous_groupe G}  (KinH : K ⊆₁ H)
  : ((K↘H): set ((H : groupe) : Type*)) = {x | x.val ∈ K} := rfl
-- ↓ Description de l'ensemble du sous groupe de G obtenu à partir d'un sous groupe de H
lemma sous_groupe_up_ens {G : groupe} {H : sous_groupe G} (K : sous_groupe H)
  : ((K : sous_groupe G) : set G) = {x | x∈H ∧ ∀p:x∈H, (⟨x,p⟩:H)∈K} := rfl

-- ↓ Lemme n°1 montrant qu'en faisant la convertion 
--       (sous_groupe de G inclus dans  --> sous_groupe de H --> sous_groupe de G)
--   on tombe sur le sous_groupe de départ
lemma sous_groupe_up_down {G : groupe} {H : sous_groupe G} (K : sous_groupe H) 
  : ((K : sous_groupe G)↘H) = K :=
begin
  rw [sous_groupe_eq_iff, ←set_eq], intro a,
  rw [sous_groupe_down_ens (ss_gr_of_ss_ss_gr_sub K)],
  split; intro p,
    rw ←subtype_eq a p.1, exact p.2 p.1,
    exact ⟨a.property, λ pp, by{have : pp=a.property :=rfl, rw this, cases a, exact p,}⟩, 
end

-- Lemme n°2 montrant qu'en faisant la convertion
--       (sous_groupe de H) --> sous_groupe de G inclus dans H --> sous_groupe de H
-- on tombe sur le sous_groupe de départ.
lemma sous_groupe_down_up {G : groupe} {H K: sous_groupe G} (KinH: K ⊆₁ H)
  : (K↘H : sous_groupe G) = K :=
begin
  rw [sous_groupe_eq_iff, ←set_eq], intro a,
  rw sous_groupe_up_ens,  
  split; intro p,
    exact p.2 p.1,
    exact ⟨(KinH.h _ p), (λ_, p)⟩, 
end


/-********************FIN Diverses définitions pour gérer les sous groupes de sous groupes************************ -/





/-************************Lien sous ensemble<-->sous groupe et sous groupes remarquables *****************************-/
/-
- Définitions principales :
  - est_sous_groupe : classe représentant la propriété d'être un sous groupe pour un ensemble
  - sous_groupe_de_est_sous_groupe : convertit un ensemble qui est_sous_groupe en sous_groupe
- Notations introduites :
  - A <₁ G pour indiquer qu'un ensemble A est un sous groupe de G
  - ↩A pour dénoter le sous_groupe induit par un ensemble A qui vérifie A <₁ G
    --> ↩ s'écrit grâce à \hookl (ou juste \hook )
    --> Cette notation n'est pas très logique, peut être trouver mieux ? 
-/


-- Cette classe permet de convertir automatiquement un ensemble qui satisfait
-- les axiomes d'un sous_groupe comme sa structure de sous groupe sous jacente
class est_sous_groupe {G: groupe} (A : set G) : Prop := 
  (inv_stab : ∀ a ∈ A, a⁻¹ ∈ A)
  (mul_stab : ∀ a b ∈ A, a*b ∈ A)
  (contient_neutre : (1:G) ∈ A)

-- Si on a une preuve qu'un sous ensemble A est un sous groupe, 
-- cette fonction retourne la structure de sous_groupe sous jacente
def sous_groupe_de_est_sous_groupe {G : groupe} (A : set G) 
  [pA : est_sous_groupe A] : sous_groupe G := ⟨A, pA.2, pA.1, pA.3⟩

-- ↓Notation pour le sous groupe. 
notation H `<₁`:51 G := @est_sous_groupe G H
-- ↓Notation pour voir un sous ensemble de G.ens comme un sous groupe. '↩' s'écrit "\hook"
notation `↩`:56 A:56 := sous_groupe_de_est_sous_groupe A

--↓ Exemple pour l'utilisation des notations : 
--↓ -Ici comme on a la preuve h que A < G dans le contexte, ↩A représente le sous groupe
--↓  d'ensemble A, et on peut définir un morphisme de ↩A verd G par exemple
example (G : groupe) (A : set G) (h : A <₁ G) := morphisme (↩A) G 
--↑ -Cette notation est là parce que je n'arrive pas à trouver un moyen de faire une 
--↑  coercion automatique de A vers ↩A (car une coercion se fait de tout élément d'un
--↑  type vers un élément d'un autre type, mais ici pas tous les ensembles peuvent être
--↑  convertis en sous_groupe, seulement ceux qui satisfont les axiomes de stabilité.)


-- L'ensemble du sous_groupe déduit par un ensemble A est A lui même
@[simp] lemma sous_groupe_de_est_sous_groupe_id {G : groupe} (A : set G)
  [pA : est_sous_groupe A] : ((↩A) : set G) = A := rfl
-- Si H est un sous_groupe de G, l'ensemble H.sous_ens vérifie "est_sous_groupe"
@[instance] lemma sous_groupe_est_sous_groupe (G : groupe) (H : sous_groupe G)
  : est_sous_groupe (H:set G) := ⟨H.inv_stab, H.mul_stab, H.contient_neutre⟩




/-
  On déclare les sous_groupes qu'on connait 
-/
@[instance] lemma triv_est_sous_groupe (G : groupe) : {1} <₁ G :=  
  by { split; intros; rw in_singleton at *; rw H, rw inv_neutre_eq_neutre, rw neutre_gauche', rw H_1 }
@[instance] lemma groupe_est_sous_groupe (G : groupe) : set.univ <₁ G :=
  by {split; intros; exact in_univ _}
@[instance] lemma ens_inter_ens_est_sous_groupe {G : groupe} (A B : set G)
  [pA : est_sous_groupe A] [pB : est_sous_groupe B] : est_sous_groupe (A∩B) :=
begin split; intros,
  exact ⟨pA.inv_stab _ H.1, pB.inv_stab _ H.2⟩,
  exact ⟨pA.mul_stab _ H.1 _ H_1.1, pB.mul_stab _ H.2 _ H_1.2⟩,
  exact ⟨pA.contient_neutre, pB.contient_neutre⟩
end
@[instance] lemma ss_gr_inter_ss_gr_est_sous_groupe (G : groupe) (A B : sous_groupe G)
  : est_sous_groupe ((A:set G)∩B) := ens_inter_ens_est_sous_groupe (A:set G) (B:set G) 


-- Pour x∈A avec A un ensemble qui est_sous_groupe, x^k ∈ A
lemma x_pow_in_sous_groupe {G: groupe} {x : G} (A : set G) [h : est_sous_groupe A]
  : x∈A → ∀ k : ℤ, x^k ∈ A :=
begin
  intros h₃ k,
  have result_for_nat : ∀ n : ℕ, x^n ∈ A,
    intro n, induction n with n hn, 
    rw pow_zero_eq_one, exact h.contient_neutre,
    rw [coe_pow_nat,int.coe_nat_succ,mul_right_pow],
    rw coe_pow_nat at hn,
    exact h.mul_stab _ hn _ h₃, 
  cases k,
    rw [← int.coe_nat_eq, ←coe_pow_nat], exact result_for_nat _,
    rw [← int.neg_of_nat_of_succ, pow_minus_eq_inv_pow],
    apply h.1,
    exact result_for_nat _,
end

/-*********************************FIN Lien entre sous ensemble et sous groupe**************************************-/






/-********************************Définitions sous_groupe engendé et groupe cyclique*********************************-/

-- Sous groupe engendré par l'extérieur
def sous_groupe_engendre {G: groupe} (A : set G) : set G :=
  ⋂ X : {X': set G // est_sous_groupe X' ∧ A ⊆ X'}, X.val

-- Sous groupe engendré par l'intérieur
def sous_groupe_engendre₂ {G: groupe} (A : set G) : set G := 
  let F := (λ a:{x//A x}×bool, if a.snd = tt then a.fst.val else a.fst.val⁻¹) in 
  {x | ∃ L : list ({x//A x}×bool), x = prod_all L F}


/-
Preuves que ces définissions définissent bien un sous groupe
-/
@[instance] lemma engendre_est_sous_groupe {G : groupe} (A : set G)
  : est_sous_groupe (sous_groupe_engendre A) :=
begin
  split; unfold sous_groupe_engendre,
  begin -- preuve que ∀ a ∈ sous_groupe_engendre A, a⁻¹ ∈ sous_groupe_engendre A
    intros, unfold Inter at *,
    intro B, exact B.property.left.inv_stab a (H B)
  end, 
  begin -- preuve que ∀ a b ∈ sous_groupe_engendre A, a*b ∈ sous_groupe_engendre A
    intros, unfold Inter at *,
    intro B, exact B.property.left.mul_stab a (H B) b (H_1 B)
  end,
  begin -- preuve que 1 ∈ sous_groupe_engendre A
    unfold Inter, intro B, exact B.property.left.contient_neutre
  end
end

@[instance] lemma engendre_est_sous_groupe₂ {G : groupe} (A : set G)
  : est_sous_groupe (sous_groupe_engendre₂ A) :=
let F := (λ a:{x//A x}×bool, if a.snd = tt then a.fst.val else a.fst.val⁻¹) in
begin
  unfold sous_groupe_engendre₂,
  split,
    begin -- Preuve que l'inverse est stable
      intros, cases H with dec_a ha, revert a, 
      induction dec_a with a' l hrec,
        intros a ha,  unfold prod_all at ha, apply Exists.intro [], unfold prod_all, 
        have h1 : 1*a = 1, rw ha, exact G.neutre_gauche 1,
        rw G.inv_unique h1,
        
        intros a ha, 
        have hx : prod_all l F = prod_all l F, refl, 
        have hy := hrec (prod_all l F) hx, 
        cases hy with b L',
        apply Exists.intro (b ++ [(⟨a'.fst, bnot a'.snd⟩ : {x// A x}×bool)]), 
        rw mul_prod_of_concat _ _ _ G.neutre_gauche G.mul_assoc,
        unfold prod_all, unfold prod_all at ha, 
        rw ha, rw G.inv_of_mul, rw L', rw G.neutre_droite,
        cases a'.snd, 
          {simp, rw G.inv_involution},
          {simp}
    end,
    begin -- Preuve que la multiplication est stable
      intros, 
      cases H with decomp_a ha, cases H_1 with decomp_b hb, 
      apply Exists.intro (decomp_a ++ decomp_b), 
      rw mul_prod_of_concat decomp_a decomp_b _ G.neutre_gauche G.mul_assoc, 
      rw ←ha, rw ←hb,
    end,
    by {apply Exists.intro [], unfold prod_all} -- G.neutre ∈ sous_groupe_engendre₂ A 
end


-- A ⊆ <A>  
lemma engendre₂_contient_ens {G : groupe} (A : set G) :
  A ⊆ sous_groupe_engendre₂ A :=
begin
  intros a h, 
  unfold sous_groupe_engendre₂, simp, 
  apply Exists.intro [prod.mk (⟨a, h⟩: {x//A x}) tt],
  unfold prod_all, simp,
  have : G.mul a 1 = a*1, refl, rw this, 
  exact (G.neutre_droite a).symm, 
end


--Preuve que les deux définitions définissent le même sous groupe
lemma engendre₂_est_engendre {G : groupe} (A : set G) :
  sous_groupe_engendre A = sous_groupe_engendre₂ A :=
begin
  apply funext, intro, apply propext, split,
  { -- sous_groupe_engendre A ⊆ sous_groupe_engendre₂ A 
    intro h, 
    unfold sous_groupe_engendre at h, unfold Inter at h, 
    let good : {X' // est_sous_groupe X' ∧ A ⊆ X'} :=
      ⟨sous_groupe_engendre₂ A, engendre_est_sous_groupe₂ A, engendre₂_contient_ens A⟩,
    have h₃ := h good, 
    simp at h₃, 
    exact h₃,
  },
  {  -- sous_groupe_engendre₂ A ⊆ sous_groupe_engendre A 
    intro h, 
    unfold sous_groupe_engendre, intro, simp, 
    unfold sous_groupe_engendre₂ at h, simp at h, 
    cases h with L,
    revert x, 
    induction L with e L hR, 
    { -- 1 appartient à tous les sous groupes contenant A 
      intro x, intro hL, 
      unfold prod_all at hL, rw hL, 
      exact i.property.1.contient_neutre,  
    },
    { -- Pour x_1,...,x_n ∈ A∪A⁻¹, x_1*x_2*...*x_n ∈ H pour tout H tq A ⊆ H < G   
      intro x, intro hL, 
      unfold prod_all at hL, 
      cases e.snd, 
      {
        simp at hL, 
        have h₀ : prod_all L (λ (a : {x // A x} × bool), ite (a.snd = tt) a.fst.val (a.fst.val)⁻¹) ∈ i.val, 
          have := hR (prod_all L (λ (a : {x // A x} × bool), ite (a.snd = tt) a.fst.val (a.fst.val)⁻¹)),
          apply this, refl, 
        have h₁ : e.fst.val ∈ i.val := (i.property.2) e.fst e.fst.property,
        have h₂ : (e.fst.val)⁻¹ ∈ i.val := i.property.1.1 _ h₁,
        rw hL,  
        exact i.property.1.mul_stab _ h₂ _ h₀, 
      }, 
      {
        simp at hL, 
        have h₀ : prod_all L (λ (a : {x // A x} × bool), ite (a.snd = tt) a.fst.val (a.fst.val)⁻¹) ∈ i.val, 
          have := hR (prod_all L (λ (a : {x // A x} × bool), ite (a.snd = tt) a.fst.val (a.fst.val)⁻¹)),
          apply this, refl,
        have h₁ : e.fst.val ∈ i.val := (i.property.2) e.fst e.fst.property,
        rw hL,
        exact i.property.1.mul_stab _ h₁ _ h₀,
      }
    }
  }
end

/-******************************FIN Définitions sous_groupe engendé et groupe cyclique*******************************-/





def centre (G : groupe) : set G := {g | ∀ h, g*h = h*g}

@[instance] lemma centre_est_sous_groupe (G : groupe) : centre G <₁ G := 
begin
  split, {
    intros a pa, intro h,
    rw [G.mul_gauche_all _ _ a, ←mul_assoc', inv_droite, neutre_gauche'],
    rw [G.mul_droite_all _ _ a, ← mul_assoc', G.mul_assoc' _ _ a],
    rw [inv_gauche', neutre_droite],
    exact (pa h).symm, 
  }, {
    intros a pa b pb, intro h,
    rw [mul_assoc', pb h, ←mul_assoc', pa h, mul_assoc'],
  }, {
    intro h, rw [neutre_droite, neutre_gauche'],
  }
end


instance ss_gr_fini_de_gr_fini {G : groupe} {H : sous_groupe G} [fG : est_fini G] : est_fini H :=
{
  majorant := fG.majorant, 
  f := λ h, fG.f h,
  f_inj :=
  begin
    intros a a' aa, 
    simp at aa, 
    have p := fG.f_inj aa,
    exact (eq_in_ss_groupe_iff_eq _ _).1 p,
  end
}

end groupe