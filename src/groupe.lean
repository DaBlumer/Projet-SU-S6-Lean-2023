


import .generique
import .cardinalite_finie
open generique


section

universe u
 


/-***************************************Définitions et coercions de base ***************************************-/
/-
- Définitions principales :
  - groupe 
  - sous_groupe G
- Coercions et notations :
  - Pour a b : G, on a les notations a⁻¹, a*b et 1
  - Pour G H un sous groupe de G, H peut être vu selon le contexte comme un groupe 
    - Dans ce cas, pour a b : H, on peut aussi écrire a*b, a⁻¹ et on peut écrire (1:H) pour le neutre
  - Pour a : G, on peut écrire a∈H pour signifier A ∈ H.sous_ens
-/


/-
Définition principale d'un groupe
- On choisit ici pour les axiomes le neutre et l'inversibilité à gauche,
les deux propriétés correspondantes à droite seront exprimées comme des
lemmes. 
- On choisit également d'exprimer l'ensemble porteur du groupe comme 
membre de la structure et non comme paramètre du type groupe (à discuter)
- Laisser la structure être une classe semble être plus pertinent que ce
qui est fait maintenant ? (à discuter)
-/
class groupe : Type (u+1) :=
  (ens : Type u)
  (mul : ens → ens → ens )
  (neutre : ens)
  (inv : ens → ens )
  (mul_assoc : ∀ a b c : ens, mul (mul a b) c = mul a (mul b c))  
  (neutre_gauche : ∀ x : ens, mul neutre x = x)
  (inv_gauche : ∀ x : ens, mul (inv x) x = neutre)



/-
coercions pour simplifier la notation : 
- Avec un groupe G, on peut écrire a : G au lieu de a : G.ens
- Avec deux éléments a, b : G.ens, on peut écrire a*b au lieu de G.mul a b
- Avec un élément a : G.ens, on peut écrire a*1 au lieu de a*G.neutre
- Enfin, avec un élément a : G.ens, on peut écrire a⁻¹ (tapé a\-1) au lieu de G.inv a 
-/
instance groupe_to_ens : has_coe_to_sort groupe (Type u) :=
  ⟨λ a : groupe, a.ens⟩

@[reducible]
instance groupe_has_mul (G : groupe) :
  has_mul (G.ens) := ⟨G.mul⟩

instance groupe_has_one (G: groupe) :
  has_one (G.ens) := ⟨G.neutre⟩

instance groupe_has_inv (G: groupe) :
  has_inv (G.ens) := ⟨G.inv⟩


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
  : has_coe_to_sort (sous_groupe G) (Type u) :=
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
local notation H `⊆₁`:52 K := sous_groupe_incl H K


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
local notation K `↘`:65 H:65 := sous_groupe_to_sous_sous_groupe H K 
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



/-************************************Définitions et notations de base morphismes********************************** -/
/-
- Définitions principales :
  - morphisme G H : représentant un mortphisme entre deux groupes.
  - comp_mor f f' : composition de morphismes (et preuve implicite que la composée de deux morphismes en est un aussi)

- Notations introduites : 
  - G →* H pour parler d'un morphisme de G vers H
-/

-- Définition d'un morphisme de groupes
structure morphisme (G H : groupe) :=
  (mor : G → H)
  (resp_mul : ∀ a b : G, mor (a*b) = (mor a) * (mor b) )

-- Notation pour le type des morphismes analogue à celle pour les fonctions: (→* est écrite avec \to*)
local notation G `→*`:51 H:51 := morphisme G H

-- Permet de voir un morphisme comme l'application sous-jacente quand c'est nécessaire
-- On peut alors écrire directement (f a) au lieu de (f.mor a)
instance morphisme_to_fonction {G H : groupe}
  : has_coe_to_fun (G  →* H) (λ _, G → H) :=
  ⟨λ m, m.mor⟩


-- Définition de la composée de deux morphismes
def comp_mor {G H K: groupe} (g : H  →* K) (f : G  →* H) : G  →* K := 
  {
    mor := g.mor∘f.mor,
    resp_mul := λ g₁ g₂, by {simp, rw [f.resp_mul, g.resp_mul]} 
  }
-- ↓ Notation pour la composée de deux morphismes, s'écrit \comp\1
-- ↓ Attention, écrire g∘f exprimera la fonction composée, sans la preuve que c'est un morphisme, 
-- ↓ et pour avoir le morphisme composé il faut faire g∘₁f
local notation g `∘₁`:51 f := comp_mor g f


/-
Différents lemmes utiles pour montrer que deux morphismes sont égaux, et pour travailler avec la composée de morphismes
-/
lemma morphisme_eq_iff {G H : groupe} (f f' : G  →* H)
  : f = f' ↔ (f : G→H) = (f' : G→H) :=
begin
  split; intro p,
    rw p,
    unfold coe_fn at p, unfold has_coe_to_fun.coe at p,
    cases f with f pf, cases f' with f' pf', simp at p,
    simp [p],
end

lemma morphisme_eq_iff₂ {G H : groupe} (f f' : G  →* H)
  : f = f' ↔ ∀ g, f g = f' g :=
begin
  split; intro p,
    rw p, intro g, refl,
    rw morphisme_eq_iff, funext, exact p x,
end

lemma comp_mor_id {G H K: groupe} (g : H  →* K) (f : G  →* H)
  : ∀ x, (g∘₁f) x = g.mor (f.mor x) := λ x, rfl
lemma mor_id {G H : groupe} (f : G  →* H)
  : ∀ x, f x = f.mor x := λ x, rfl

/-**********************************FIN Définitions et notations de base morphismes******************************** -/



/-**************************************EXEMPLES coercions et notations diverses*********************************** -/
section -- exemples d'utilisation transparente des coercions

variables (G G' G'': groupe) (H : sous_groupe G)

-- ici G est vu comme G.ens, G' comme G'.ens et H comme {a : G.ens // a∈H.sous_ens}
variables (g₁ g₂ : G) (g₁' g₂' : G') (h₁ h₂ : H) 

variables (f : G  →* G') (g : G' →* G'') (h : G' →* H)

example : G' := f g₁ -- ici f est vu comme f.mor

/-
Dans cet exemple plusieures inférences intérviennent : 
1) Comme f est utilisée comme fonction, f est vue comme f.mor
2) Comme g₁ : G.ens et que G.ens a une instance de has_mul, * est interpété comme G.mul
3) Comme on veut appliquer G.mul à h₁ : {a : G.ens // a∈H.sous_ens}, h₁ est vu comme h₁.val : G.ens
-/
example : G' := f (g₁*h₁) 

-- Ici G est vu comme G.ens, H comme {a : G.ens // a∈H.sous_ens}
-- et on peut définir l'application composée des deux morphismes simplement : 
example : G → H := h∘f
-- Pour avoir le morphisme composé :
example : G →* H := h∘₁f


end -- fin exemples
/-***********************************FIN EXEMPLES coercions et notations diverses******************************** -/




-- permet d'avoir accès à tous les théorèmes sous le même nom que la structure
-- permet également de "cacher" nos noms de théorèmes pour éviter les conflits 
namespace groupe


/-****************************************Lemmes de base pour les groupes****************************************** -/


-- Réécriture des axiomes en tant que lemmes avec les notations * ⁻¹ et 1.
-- TODO : éviter le ' en faisant la définition d'un groupe en deux temps OU en renommant les axiomes dans la déf
lemma mul_assoc' (G : groupe) (a b c : G) : a * b * c = a * (b * c) := G.mul_assoc a b c
lemma inv_gauche' (G : groupe) (a : G) : a⁻¹*a = 1 := G.inv_gauche a
lemma neutre_gauche' (G : groupe) (a : G) : 1*a = a := G.neutre_gauche a



/-
Différents lemmes utiles :
-/

lemma inv_droite (G: groupe) : ∀ a : G.ens, a * a⁻¹ = 1 :=
  begin
  intro,
  have h₁ : (a * a⁻¹)*(a * a⁻¹) = (a * a⁻¹),
    rw [mul_assoc', ← G.mul_assoc' a⁻¹, G.inv_gauche', G.neutre_gauche'],
  have h₂ := G.inv_gauche' (a * a⁻¹),
  rw [←h₁,← G.mul_assoc' _ (a*a⁻¹) (a*a⁻¹), h₁] at h₂,
  rw [inv_gauche', neutre_gauche'] at h₂,
  exact h₂,
  end


lemma neutre_droite (G : groupe) : ∀ a : G.ens, a*1 = a :=
 begin
 intro a,
 rw ← inv_gauche' G a, 
 rw ← mul_assoc',
 rw inv_droite,
 rw neutre_gauche',
 end


lemma neutre_unique {G: groupe} (e : G.ens) (h : ∀ a, e*a = a ) : e = 1 :=
  begin
  have h1 := h 1,
  rw neutre_droite at h1,
  rwa h1,
  end


lemma inv_unique (G: groupe) {a : G} {b : G} (h: b*a = 1) : b = a⁻¹ :=
  begin
  rw ← neutre_droite G b,
  rw ← inv_droite G a,
  rw ← mul_assoc',
  rw h,
  rw neutre_gauche',
  end


lemma inv_involution (G : groupe) (a : G) : (a⁻¹)⁻¹ = a :=
  begin
  rw ← neutre_droite G a⁻¹⁻¹,
  rw ← inv_gauche' G a,
  rw ← mul_assoc',
  rw inv_gauche' G a⁻¹,
  rw neutre_gauche',
  end


lemma mul_droite_div_droite (G : groupe) (a b c : G) : a * b = c ↔ a = c * b⁻¹ :=
  begin
  split,
  intro h,
  rw ← h,
  rw mul_assoc' G a b b⁻¹,
  rw inv_droite G b,
  rw neutre_droite,
  intro h,
  rw h,
  rw mul_assoc' G c b⁻¹ b,
  rw inv_gauche',
  rw neutre_droite,
  end


lemma mul_gauche_div_gauche (G : groupe) (a b c : G) : a * b = c ↔ b = a⁻¹ * c :=
  begin
  split,
  intro h,
  rw ← h,
  rw ← mul_assoc' G a⁻¹ a b,
  rw inv_gauche' G a,
  rw neutre_gauche',
  intro h,
  rw h,
  rw ← mul_assoc',
  rw inv_droite,
  rw neutre_gauche',
  end


lemma inv_of_mul (G: groupe) (a b : G) : (a*b)⁻¹ = b⁻¹ * a⁻¹ :=
  begin
  rw ← mul_gauche_div_gauche,
  rw ← neutre_droite G a⁻¹,
  rw ← mul_gauche_div_gauche,
  rw ← mul_assoc',
  rw inv_droite,
  end


lemma mul_droite_all (G : groupe) (a b c : G) : a=b ↔ a*c = b*c :=
  begin
  split,
  intro h,
  rw h,
  intro h,
  rw mul_droite_div_droite at h,
  rw  [mul_assoc', inv_droite, neutre_droite] at h, 
  exact h,
  end


lemma mul_gauche_all (G: groupe) (a b c : G) : (a=b) ↔ (c*a = c*b) :=
  begin
  split,
  intro h,
  rw h,
  intro h,
  rw mul_gauche_div_gauche at h,
  rw ← mul_assoc' at h,
  rw h,
  rw inv_gauche',
  rw neutre_gauche'
  end


lemma inv_neutre_eq_neutre (G : groupe) : (1:G)⁻¹=1 := 
  by {rw [G.mul_gauche_all _ _ 1, inv_droite, neutre_droite],}


lemma eq_of_inv_eq (G : groupe) (a b : G) : (a⁻¹=b⁻¹) ↔ (a=b) :=
  begin
    split; intro h; try {rw h}, 
    rw [←G.neutre_droite a⁻¹,mul_gauche_div_gauche] at h,
    rw [inv_involution, ← mul_droite_div_droite, neutre_gauche'] at h,
    rw h,
  end


lemma mul_right_inv_eq_one_of_eq (G : groupe) (a b : G) : (a=b) ↔ (a*b⁻¹ = 1) :=
  begin
  split;intro h,
    rw h, exact inv_droite _ _,
    rw [mul_droite_div_droite, inv_involution, neutre_gauche'] at h, exact h,
  end


lemma mul_left_inv_eq_one_of_eq (G : groupe) (a b : G) : (a=b) ↔ (b⁻¹*a = 1) :=
  begin
  split;intro h,
    rw h, exact inv_gauche' _ _,
    rw [mul_gauche_div_gauche, inv_involution, neutre_droite] at h, exact h,
  end


lemma neutre_unique_fort (G : groupe) (e a : G) (h : e*a = a) : e = 1 :=
  by {rw [mul_droite_div_droite, inv_droite] at h, exact h}

/-**************************************FIN Lemmes de base pour les groupes**************************************** -/



/-***************************************Lemmes de base pour les morphismes***************************************** -/

lemma mor_resp_mul {G H : groupe} {f : G  →* H}
  : ∀ a b : G, f (a * b) = f a * f b := λ a b, f.resp_mul a b 

lemma mor_fun_eq {G H : groupe} (f : G  →* H) : (f : G→H) = f.mor := rfl

lemma comp_mor_fun_eq {G H K: groupe} (g : H  →* K) (f : G  →* H)
  : (g∘₁f : G→K) = ((g:H→K) ∘ (f:G→H)) := rfl 

lemma mor_neutre_est_neutre {G H : groupe} {f : G  →* H} : f 1 = 1 :=
begin
  apply H.neutre_unique_fort (f 1) (f 1),
  rw [← mor_resp_mul, G.neutre_droite],
end

theorem mor_inv_inv_mor {G H : groupe} {f : G  →* H}  (a : G) : f a⁻¹ =  (f a)⁻¹ :=
  begin
  apply inv_unique,
  rw ← mor_resp_mul a⁻¹ a,
  rw inv_gauche',
  rw mor_neutre_est_neutre,
  end

/-**************************************FIN Lemmes de base pour les morphismes************************************** -/






/-*********************************Définition de lemmes de calcul pour les puissances********************************-/
/-
- Définitions principales :
  - puissance_n : la puissance d'un élément du groupe par un entier naturel (ℕ) 
  - puissance_z : la puissance d'un élément du groupe par un entier relatif (ℤ)
- Notations introduites :
  - x^k avec k un entier naturel OU un entier relatif 
-/


/-
Définitions des deux fonctions de puissance et des notations
-/
def puissance_n {G : groupe} (x : G) : ℕ → G
  | nat.zero := 1
  | (nat.succ n) :=  x*(puissance_n n)

instance {G : groupe} : has_pow G ℕ := ⟨puissance_n⟩    

def puissance_z {G : groupe} (x : G) : ℤ → G
  | (int.of_nat n) := x^n
  | (int.neg_succ_of_nat n) := (x^(n+1))⁻¹

instance {G : groupe} : has_pow G ℤ := ⟨puissance_z⟩




-- Lemme montrant la cohérence entre la puissance par un naturel et un relatif
lemma coe_pow_nat {G : groupe} {n : ℕ} (x : G) : x ^ n = x ^ (n:ℤ) :=
  begin
    rw int.coe_nat_eq, 
    unfold pow,
    unfold puissance_z,
    unfold pow, 
  end




/-
Différents lemmes de calculs avec les puissances 
-/
lemma self_eq_pow_one {G : groupe} (x : G) : x = x^1 :=
  begin
    unfold pow, unfold puissance_n, apply eq.symm, exact G.neutre_droite x,  
  end

lemma pow_zero_eq_one {G : groupe} (x : G) : x^0 = 1 :=
  begin
    unfold pow, unfold puissance_n, 
  end

lemma pow_minus_one_eq_inv {G : groupe} (x : G) : x^(-1 : ℤ) = x⁻¹ :=
  begin
    unfold pow,
    have : -1 = -[1+ 0], refl, rw this, 
    unfold puissance_z,
    rw nat.zero_add, rw ← self_eq_pow_one,  
  end

lemma mul_of_n_pow_comm {G : groupe} (x : G) (n : ℕ): x * (x^n) = x^n * x :=
  begin
    induction n with n hn,
    rw [pow_zero_eq_one, neutre_droite], apply eq.symm, rw neutre_gauche', 
    unfold pow at *, unfold puissance_n,
    rw mul_assoc', 
    rw hn,
  end

lemma mul_of_z_pow_comm {G : groupe} (x : G) (n : ℤ) : x * (x^n) = x^n * x :=
  begin
    cases n, 
    rw ← int.coe_nat_eq,
    rw ← coe_pow_nat, 
    exact mul_of_n_pow_comm x n, 
    unfold pow, unfold puissance_z, 
    rw mul_droite_div_droite, rw inv_involution,
    rw mul_assoc', 
    rw mul_of_n_pow_comm, 
    rw ← mul_assoc',
    rw inv_gauche', 
    rw neutre_gauche', 
  end

lemma mul_left_pow {G : groupe} {n : ℤ} (x : G) : (x ^ (n+1)) = x*(x^n) :=
  begin
    cases n,
    {
      conv { to_lhs, rw ← int.coe_nat_eq }, 
      rw int.coe_nat_add_one_out,
      rw ← coe_pow_nat,
      unfold pow, unfold puissance_n, unfold puissance_z, unfold pow,
    },
    {
      cases n, 
      {
        have h : -[1+ 0] + 1 = 0 := by refl, rw h,
        have h₂ : (0 : ℤ) = int.of_nat 0, refl, rw h₂,
        unfold pow, unfold puissance_z,
        rw [nat.add_succ, nat.add_zero],
        rw ← self_eq_pow_one,
        rw inv_droite,
        rw pow_zero_eq_one,  
      },
      {
        have h : -[1+ n.succ] +1 = -[1+ n], refl, rw h,
        unfold pow, unfold puissance_z, 
        unfold pow, unfold puissance_n,

        conv {to_lhs, rw inv_of_mul},
        simp only [mul_of_n_pow_comm],
        rw inv_of_mul,
        rw ← G.mul_assoc,
        rw ← mul_droite_all,
        have hh := mul_of_n_pow_comm x n, simp at hh, unfold pow at hh, 
        rw hh,  
        rw inv_of_mul,
        rw ← G.mul_assoc, 
        have hh' := G.inv_droite, simp at hh', 
        rw hh' x, 
        have hh'' : 1 = G.neutre, refl, rw hh'', 
        rw G.neutre_gauche,
      }
    } 
  end


lemma mul_right_pow  {G : groupe} {n : ℤ} (x : G) : (x ^ (n+1)) = (x^n)*x :=
  begin 
    rw mul_left_pow,
    rw ← mul_of_z_pow_comm,
  end

lemma pow_mul_pow {G : groupe} {n m : ℤ} (x : G) : (x^n)*(x^m) = x^(n+m) :=
  begin
    cases m, 
    { -- m ≥ 0 
      induction m with k hk,
        {
          rw [← int.coe_nat_eq, ← coe_pow_nat],
          rw pow_zero_eq_one,
          rw neutre_droite, 
          rw [int.coe_nat_zero, int.add_zero],
        },
        {
          --rw [← int.coe_nat_eq, ← coe_pow_nat],
          unfold pow at *, unfold puissance_z at *,
          unfold pow at *, unfold puissance_n at *,
          have h := mul_of_n_pow_comm x, unfold pow at h, 
          rw [h, ← mul_assoc'],
          rw hk,
          have iden : n + int.of_nat k.succ = n + k + 1,
            rw [← int.coe_nat_eq, int.coe_nat_succ, int.add_assoc],
          rw iden, 
          have h₂ := mul_right_pow x, unfold pow at h₂, 
          rw h₂, 
          rw int.coe_nat_eq, 
        },
    },
    { -- m < 0
      induction m with k hk,
      {
        unfold pow, unfold puissance_z,
        rw nat.zero_add, rw ← self_eq_pow_one,
        rw mul_droite_div_droite, rw inv_involution,
        have h₂ := mul_right_pow x, unfold pow at h₂, rw ← h₂,
        have : n + -[1+ 0] + 1 = n,
          rw int.add_assoc, have : -[1+0]=-1, refl, rw this, 
          rw int.add_left_neg, rw int.add_zero, 
        rw this, 
      },
      {
        unfold pow at *, unfold puissance_z at *,
        rw [coe_pow_nat, int.coe_nat_add, int.coe_nat_one, mul_left_pow],
        rw [inv_of_mul, ← mul_assoc'], 
        rw ← coe_pow_nat, 
        rw hk, 
        rw mul_droite_div_droite, rw inv_involution, 
        have h₂ := mul_right_pow x, unfold pow at h₂, rw ← h₂,
        have : (n + -[1+ k]) =  (n + -[1+ k.succ] + 1),
          have : ∀ z, -[1+ z] = -z.succ, intro, refl,
          repeat{rw this},
          repeat{rw ← int.coe_nat_add_one_out},
          repeat{rw int.neg_add},
          rw [int.add_assoc n _ 1, int.add_assoc _ (-1) 1], 
          rw [int.add_left_neg, int.add_assoc, int.add_zero], 
      }
    }
  end

lemma pow_minus_eq_inv_pow {G : groupe} {n : ℤ} (x : G) : x^(-n) = (x^n)⁻¹ :=
  begin
    rw ← G.neutre_gauche' (x ^ n)⁻¹,
    rw ← mul_droite_div_droite,
    rw pow_mul_pow,
    rw int.add_left_neg,
    rw [←int.coe_nat_zero, ←coe_pow_nat, pow_zero_eq_one],
  end

lemma one_pow_eq_one {G : groupe} (n : ℤ) : (1:G)^n = 1 :=
begin
  have one_pow_eq_one_nat : ∀ k : ℕ , (1:G)^k = 1, intro, induction k with k hk,
    {rw pow_zero_eq_one}, -- initialisation
    {rw [coe_pow_nat, int.coe_nat_succ, mul_left_pow, neutre_gauche', ←coe_pow_nat,hk]}, -- recurrence
  cases n,
  { -- n ≥ 0
    rw [← int.coe_nat_eq, ← coe_pow_nat],
    exact one_pow_eq_one_nat _,
  },
  { -- -[1+ n]
    have : -[1+ n] = -n.succ, refl, rw this,
    rw [pow_minus_eq_inv_pow, ← coe_pow_nat],
    rw one_pow_eq_one_nat _,
    rw [G.mul_droite_all (1⁻¹) 1 1, inv_gauche', neutre_droite],
  }

end


lemma pow_pow {G : groupe} {n m : ℤ} (x : G) : (x^n)^m = (x^(n*m)) :=
  begin
    -- On commence par montrer la version avec m positif, on lui donne un nom car on la
    -- réutilise dans le cas négatif
    have pow_pow_pos : ∀ k : ℕ, (x^n)^k = (x^(n*k)),
    {
      intro k,
      induction k with k hk, 
      { -- m = 0
        rw [int.coe_nat_zero, int.mul_zero],
        rw [← int.coe_nat_zero, ← coe_pow_nat, pow_zero_eq_one, pow_zero_eq_one]
      },
      { -- m = k + 1 
        rw [int.coe_nat_succ, int.distrib_left, int.mul_one],
        rw [coe_pow_nat, int.coe_nat_succ, mul_right_pow (x^n), ← coe_pow_nat], 
        rw ← pow_mul_pow,
        rw hk,
      }
    },
    cases m, 
    { -- m ≥ 0
      rw [← int.coe_nat_eq, ← coe_pow_nat],
      exact pow_pow_pos _, 
    },
    { -- m < 0
      have : -[1+ m] = -m.succ := rfl, rw this,
      have neg_of_mul_neg : ∀ a b : ℤ, a * -b = -(a*b),
        intros, rw int.neg_eq_neg_one_mul, conv {to_rhs, rw int.neg_eq_neg_one_mul},
        rw [← int.mul_assoc, int.mul_comm a (-1), int.mul_assoc],
      rw neg_of_mul_neg,
      rw pow_minus_eq_inv_pow, rw pow_minus_eq_inv_pow,
      rw [← coe_pow_nat, pow_pow_pos],
    }
  end

/-*******************************FIN Définition de lemmes de calcul pour les puissances******************************-/






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
local notation H `<₁`:51 G := @est_sous_groupe G H
-- ↓Notation pour voir un sous ensemble de G.ens comme un sous groupe. '↩' s'écrit "\hook"
local notation `↩`:56 A:56 := sous_groupe_de_est_sous_groupe A

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





/-*****************************************Sous groupes distingues et exemples ****************************************-/
/-
- Définitions principales :
  - mul_gauche_ens pour définir gH
  - mul_droite_ens pour définir Hg
  - est_distingue pour indiquer qu'un sous groupe Hest distingué 
- Notations introduites : 
  - H ⊲ G pour dire que Hest ditingué dans G. ⊲ s'écrit grâce à \vartr  
  - Pour la multiplication à droite, g*₂H.Et pour la multiplication à gauche, H*₃g
    --> On ne peut pas utiliser * qui est prise par has_mul, et has_mul nécessite que les deux opérandes soient de même type.
-/


/-
Définitions de gH et Hg et notations pour ces deux multiplications 
-/
def mul_gauche_ens {G : groupe} (a : G) (H : set G) : set G :=
  {g : G | ∃ h ∈ H, g = a*h}
def mul_droite_ens {G : groupe} (H : set G) (a : G) : set G :=
  {g : G | ∃ h ∈ H, g = h*a}

local notation a ` *₂ `:51 H:51 :=  mul_gauche_ens a H
local notation H ` *₃ `:51 a:51 := mul_droite_ens H a



/-
- Classe représentant une preuve qu'un sous groupe est distingué 
- On choisit comme définition H ⊲ G ↔ ∀ g : G, gH = Hg   
- C'est une classe pour permettre à lean de déduire une telle instance du contexte pour certains théorèmes (par
  exemple, dans le thèorème d'isomorphisme 1, pas besoin de dire explicitement que ker f est distingué, lean le saura seul)
-/
class est_distingue {G : groupe} (H : sous_groupe G) : Prop :=
  (h : ∀ a:G, a *₂ H = H *₃ a)
-- ↓ Notation canonique pour un sous groupe qui est distingué. ⊲ s'écrit \vartr  
local notation H `⊲`:51 G := @est_distingue G H


/-
Déclarations des groupes distingués connus ({1} et G lui même)
-/
@[instance] lemma triv_est_distingue (G : groupe) : ((↩{1}) ⊲ G) :=
begin
  split, intro, rw ←set_eq, intro, split; intro p;
  cases p with h tmp; cases tmp with h_H peq; simp at h_H; rw in_singleton at h_H; rw h_H at *;
  rw [neutre_droite, ← G.neutre_gauche' a] at peq<|>rw [neutre_gauche', ← G.neutre_droite a] at peq;
  existsi (1:G); existsi ((↩{1}):sous_groupe G).contient_neutre; 
  exact peq, 
end
@[instance] lemma groupe_est_distingue (G : groupe) : ((↩set.univ) ⊲ G) :=
begin 
  split, intro, rw ←set_eq, intro, split; intro p;
  cases p with h tmp; cases tmp with h_H peq; simp at h_H,
    {existsi a*h*a⁻¹, existsi true.intro,
    rw [peq,mul_assoc', mul_assoc', inv_gauche', neutre_droite]},
    existsi a⁻¹*h*a, existsi true.intro,
    rw [peq, ←mul_assoc', ←mul_assoc', inv_droite, neutre_gauche'],
end


-- Caractérisation utile pour travailler avec les sous groupes distingués
lemma carac_est_distingue {G : groupe} (H' : sous_groupe G)
  : est_distingue H' ↔ ∀ h ∈ H', ∀ g : G, g*h*g⁻¹ ∈ H'  :=
begin
  split, {
    intros dis_H h h_in_H g,
    cases dis_H,
    have hg := dis_H g,
    rw ←set_eq at hg, 
    have h₁ : g*h ∈ g *₂ ↑H',
      apply Exists.intro h, apply Exists.intro h_in_H, refl, 
    have h₂ := (hg (g*h)).1 h₁, 
    cases h₂ with h' tmp, cases tmp with h'_in_H h₃,
    rw G.mul_droite_all _ _ g⁻¹ at h₃,
    rw h₃,
    rw [mul_assoc', inv_droite, neutre_droite],
    exact h'_in_H,
  }, {
    intro P, split, intro g,
    rw ← set_eq, intro a,
    split;intro tmp; cases tmp with h tmp; cases tmp with h_in_H h_eq,
    {
      apply Exists.intro (g*h*g⁻¹), apply Exists.intro (P h h_in_H g),
      repeat {rw mul_assoc'}, rw [inv_gauche', neutre_droite],
      exact h_eq,
    }, {
      apply Exists.intro (g⁻¹*h*(g⁻¹)⁻¹), apply Exists.intro (P h h_in_H g⁻¹),
      repeat {rw ←mul_assoc'}, rw [inv_droite, inv_involution, neutre_gauche'],
      exact h_eq,
    }
  }
end


-- On montre que si K ⊲ G, et que K ⊆ H, alors K ⊲ H 
@[instance] lemma distingue_down_est_distingue {G : groupe} {H K : sous_groupe G}
  (HinK : H ⊆₁ K) [dH : est_distingue H] : est_distingue (H↘K) :=
begin
  rw carac_est_distingue,
  intros k hk g,
  rw [mem_ss_groupe_simp, sous_groupe_down_ens] at ⊢ hk,
  have goal : (g*k*g⁻¹).val∈H,
    repeat{rw coe_mul_sous_groupe},
    rw carac_est_distingue at dH,
    exact dH k.val hk g.val,
  exact goal,
end


-- Utile lorsqu'on veut passer d'une expression du type h*g à une du type g*h'
lemma distingue_droite_to_gauche {G : groupe } {H' : sous_groupe G}
  (dH : est_distingue H') (h ∈ H') (g : G) : ∃ h' ∈ H', g*h = h'*g :=
begin
  apply Exists.intro (g*h*g⁻¹),
  apply Exists.intro ((carac_est_distingue H').1 dH _ H g),
  repeat {rw mul_assoc'}, rw [inv_gauche', neutre_droite],
end

/-***************************************FIN Sous groupes distingues et exemples **************************************-/




/-****************************************Ensemble quotient et groupe quotient ****************************************-/
/-
- Définitions principales :
  - rel_gauche_mod et rel_droite_mod : les deux relations d'équivalence modulo un sous groupe
    - Notation utilisée : G%.H pour rel_gauche_mod et H.%G pour rel_droite_mod
  - quotient_gauche et quotient_droite : les deux types quotient
    - Notation utilisée : G /. H pour quotient_gauche et H .\ G pour quotient_droite
  - groupe_quotient : si H ⊲ G, le groupe quotient de G sur H
    - Notation utilisée : G /* H
  - mor_quotient : le morphisme naturel de G vers G/*H qui renvoie chaque élément à sa classe
  - repr_quot : application de G/*H vers G qui associe à chaque classe un représentant arbitraire.
-/

def rel_gauche_mod {G : groupe} (H : sous_groupe G) : G → G → Prop :=
  λ x y : G, y ∈ x *₂ H 
def rel_droite_mod {G : groupe} (H : sous_groupe G) : G → G → Prop :=
  λ x y : G, y ∈ ↑H *₃ x 

local notation G ` %. `:35 H:34 := rel_gauche_mod H
local notation H ` .% `:35 G:34 := rel_droite_mod H


lemma distingue_gde {G:groupe} {H : sous_groupe G} (dH : est_distingue H)
  : (G %. H) = (H .% G) :=
  begin
    unfold rel_droite_mod, 
    rw rel_gauche_mod, unfreezingI{cases dH},
    apply funext, intro, apply funext, intro y,  rw dH, 
  end

lemma rel_gauche_carac₁ {G : groupe} (H : sous_groupe G) (a b : G)
  : rel_gauche_mod H a b ↔ a *₂ H = b *₂ H :=
begin
  split; intro p, {
    cases p with h tmp, cases tmp with h_H b_ah,
    rw ←set_eq, intro g,
    split;intro g_in; cases g_in with h₂ tmp; cases tmp with h₂_H g_ab_h, {
      have p := b_ah.symm, rw [mul_droite_div_droite] at p, rw p at g_ab_h,
      existsi h⁻¹*h₂, existsi H.mul_stab _ (H.inv_stab _ h_H) _ h₂_H,
      rw [g_ab_h, mul_assoc'],
    }, {
      rw b_ah at g_ab_h,
      existsi h*h₂, existsi H.mul_stab _ h_H _ h₂_H,
      rw [g_ab_h, mul_assoc'],
    }
  }, {
    unfold rel_gauche_mod, rw p, 
    existsi [(1:G), H.contient_neutre],
    rw neutre_droite, 
  }
end

lemma rel_gauche_carac₂ {G : groupe} (H : sous_groupe G) (a b : G) {h h' : H}
  (p : a*h = b*h') : rel_gauche_mod H a b :=
begin
  have p' := p.symm,
  rw [mul_droite_div_droite, mul_assoc'] at p',
  existsi ((h:G)*(h':G)⁻¹), existsi (H.mul_stab _ h.property _ (H.inv_stab _ h'.property)), 
  exact p',
end

lemma rel_gauche_refl {G : groupe} (H : sous_groupe G) (a : G) 
  : (G %. H) a a :=
begin
    apply Exists.intro (1:G), rw G.neutre_droite,
    apply Exists.intro H.contient_neutre, refl,
end

lemma rel_gauche_symm {G : groupe} (H : sous_groupe G) (a b: G) 
  : (G %. H) a b →  (G %. H) b a :=
begin
  intro hxy, cases hxy with g hg, cases hg with hg eg,
  have ge := eg.symm, 
  rw ← (G.mul_droite_div_droite a g b).symm at ge,
  apply Exists.intro g⁻¹, apply Exists.intro (H.inv_stab g hg),
  exact ge,
end

lemma rel_gauche_trans {G : groupe} (H: sous_groupe G) (a b c : G)
  : (G %. H) a b → (G %. H) b c → (G %. H) a c :=
begin
  intros hxy hyz, cases hxy with g hg, cases hyz with g₂ hg₂,
  cases hg with hg eg, cases hg₂ with hg₂ eg₂, 
  rw eg at eg₂, rw G.mul_assoc' _ g g₂ at eg₂,
  apply Exists.intro (g*g₂), apply Exists.intro (H.mul_stab g hg g₂ hg₂),
  exact eg₂,
end



lemma distingue_rels_equiv { G : groupe} {H : sous_groupe G} 
  (dH : est_distingue H) : (G %. H) = (H .% G) :=
begin
  unfold rel_gauche_mod, unfold rel_droite_mod,
  apply funext,
  intro, apply funext, intro, 
  rw dH.h,
end

lemma mul_induite_bien_def {G: groupe} {H: sous_groupe G} (dH: est_distingue H)
  {a b c d : G} (rac : (G %. H) a c) (rbd : (G %. H) b d)
  : (G %. H) (a*b) (c*d) :=
begin
  intros, cases rac with h₁ eq₁, cases rbd with h₂ eq₂,
  cases eq₁ with a₁ eq₁, cases eq₂ with a₂ eq₂,
  rw G.mul_droite_all c (a*h₁) a⁻¹ at eq₁,
  have a₃ : a*h₁*a⁻¹ ∈ H, exact (carac_est_distingue H).elim_left dH h₁ a₁ a, 
  rw G.mul_droite_div_droite c a⁻¹ (a*h₁*a⁻¹) at eq₁, rw G.inv_involution at eq₁, 
  rw G.mul_droite_all c _ d at eq₁, rw eq₂ at eq₁, rw G.mul_assoc' _ a (b*h₂) at eq₁,
  rw ← G.mul_assoc' a b h₂ at eq₁, rw ← eq₂ at eq₁, 
  rw ← G.mul_assoc' (a*h₁*a⁻¹) (a*b) h₂ at eq₁,
  rw ← G.inv_involution h₂ at eq₁, rw ← G.mul_droite_div_droite (c*d) h₂⁻¹ _ at eq₁,
  have a₂' : h₂⁻¹ ∈ H, exact H.inv_stab h₂ a₂, 
  cases distingue_droite_to_gauche dH (h₂⁻¹) a₂' (c*d) with h₄ a₄,
  cases a₄ with a₄ eq₃,
  rw eq₃ at eq₁, 
  rw G.mul_gauche_div_gauche h₄ at eq₁, rw ← G.mul_assoc' h₄⁻¹ at eq₁, 
  have a₅ : h₄⁻¹ * (a * h₁ * a⁻¹) ∈ H, 
    apply H.mul_stab, apply H.inv_stab, assumption, assumption, 
  have af : h₄⁻¹ * (a * h₁ * a⁻¹) * (a * b) ∈ mul_droite_ens (H:set G) (a*b), 
    apply Exists.intro (h₄⁻¹ * (a * h₁ * a⁻¹)), apply Exists.intro a₅, refl, 
  rw ← dH.h (a*b) at af, cases af with h₆ a₆, cases a₆ with a₆ eq₄, 
  rw eq₄ at eq₁, 
  apply Exists.intro h₆, apply Exists.intro a₆, assumption,  
end  

def quotient_gauche {G : groupe} (H : sous_groupe G) 
  := quot (G %. H)
def quotient_droite {G : groupe} (H : sous_groupe G)
  := quot (H .% G)

instance g_has_quotient_gauche {G: groupe}  : has_quotient_gauche G (sous_groupe G)
  := ⟨λ H, quotient_gauche H⟩
instance g_has_quotient_droite {G: groupe} : has_quotient_droite G (sous_groupe G)
  := ⟨λ H, quotient_droite H⟩
 
local notation `⟦`:max a`⟧@`:max H:max := quot.mk (rel_gauche_mod H) a 

def classes_equiv_gauche {G : groupe} (H : sous_groupe G) :=
  {X // ∃ a : G, X = mul_gauche_ens a H}

def elem_to_classe_gauche {G : groupe} (H : sous_groupe G)
  (x : G) : classes_equiv_gauche H := 
{
  val := mul_gauche_ens x H,
  property := by {apply Exists.intro x, refl,}
}

lemma e_to_cg_resp_rel {G : groupe} (H : sous_groupe G) (a b : G) (a_b : (G %. H) a b) 
  : elem_to_classe_gauche H a = elem_to_classe_gauche H b :=
begin
  unfold elem_to_classe_gauche,
  apply subtype.eq, simp, 
  rw ← rel_gauche_carac₁, exact a_b,
end

def quot_to_classe_gauche {G : groupe} (H : sous_groupe G) : (G/.H) → classes_equiv_gauche H :=
  quot.lift (elem_to_classe_gauche H) (e_to_cg_resp_rel H)

def bij_classes_equiv_quot {G : groupe} (H : sous_groupe G)
  : bijection (G /. H) (classes_equiv_gauche H) :=
{
  val := quot_to_classe_gauche H,
  property :=
  begin
    split, { -- Injective
      intros a₁ a₂ p, 
      unfold quot_to_classe_gauche at p,
      cases quot.exists_rep a₁ with g₁ g_a₁,
      cases quot.exists_rep a₂ with g₂ g_a₂,
      rw [←g_a₁, ←g_a₂] at *,
      simp at p,
      unfold elem_to_classe_gauche at p,
      apply quot.sound,
      rw subtype.mk.inj_eq at p,
      rw rel_gauche_carac₁,
      exact p,
    }, { -- Surjective
      intro B, 
      cases B.property with b B_bH,
      existsi (quot.mk _ b),
      unfold quot_to_classe_gauche,
      unfold elem_to_classe_gauche,
      apply subtype.eq, simp,
      rw B_bH,
    }
  end
}

lemma quot_to_classe_gauche_id {G : groupe} (H : sous_groupe G)
  (a : G) : (quot_to_classe_gauche H (quot.mk _ a)).val = a *₂ H := rfl

lemma quot_to_classe_gauche_id₂ {G : groupe} (H : sous_groupe G)
  (a : G) : (quot_to_classe_gauche H (quot.mk _ a)) = ⟨a *₂ H, (quot_to_classe_gauche H (quot.mk _ a)).property⟩ := rfl

lemma quot_to_classe_gauche_prop {G : groupe} {H : sous_groupe G}
  : function.bijective (quot_to_classe_gauche H) := (bij_classes_equiv_quot H).property

noncomputable def repr_quot {G : groupe} {H : sous_groupe G} (a : G/.H) : {g // (⟦g⟧@H) = a} :=
  ⟨choose (quot.exists_rep a), prop_of_choose (quot.exists_rep a)⟩

lemma class_of_repr_quot {G : groupe} {H : sous_groupe G} (a : G/.H)
  : (⟦repr_quot a⟧@H) = a := (repr_quot a).property


lemma quot_gauche_exact {G : groupe} {H : sous_groupe G} (a b : G)
   (p : (⟦a⟧@H) = (⟦b⟧@H)) : rel_gauche_mod H a b :=
begin
  have p' := eq.refl (quot_to_classe_gauche _ (⟦a⟧@H)),
  conv at p' {to_rhs, rw p},
  rw [quot_to_classe_gauche_id₂] at p',
  conv at p' {to_rhs, rw quot_to_classe_gauche_id₂},
  rw subtype.mk.inj_eq at p', 
  rw rel_gauche_carac₁,
  exact p', 
end

def mul_partielle_gauche_ {G : groupe} {H : sous_groupe G} (a : G)
  : G → (G/.H) :=
  λ b, quot.mk (G %. H) (a*b)

def mul_partielle_gauche_quotient_ {G: groupe} (H: sous_groupe G) {dH: est_distingue H} (a : G)
  : (G/.H) → (G/.H) :=
  @quot.lift G (G %. H) (G/.H) (mul_partielle_gauche_ a) (λ b c, 
    begin
      intro h, 
      have h₂ : (G %. H) a a, exact rel_gauche_refl H a, 
      have : (G %. H) (a*b) (a*c), exact mul_induite_bien_def dH h₂ h,
      unfold mul_partielle_gauche_, 
      rw quot.sound this, 
    end
  )

def mul_quotient_ {G: groupe} {H: sous_groupe G} (dH : est_distingue H)
  : (G /. H) → (G /. H) → (G /. H) :=
  @quot.lift G (G %. H) (G/.H → G/.H) 
   (@mul_partielle_gauche_quotient_ G H dH) (λ a b, 
  begin
    intro h, unfold mul_partielle_gauche_quotient_,
    have :  @mul_partielle_gauche_ G H a  = mul_partielle_gauche_ b, 
    apply funext, intro, unfold mul_partielle_gauche_, 
    have h₂ : (G %. H) x x, exact rel_gauche_refl H x,
    have : (G %. H) (a*x) (b*x), exact mul_induite_bien_def dH h h₂,
    rw quot.sound this, 
    simp only [this], 
  end
  )

def inv_quotient_ {G : groupe} {H: sous_groupe G} (dH: est_distingue H) 
  : (G/.H) → (G/.H) :=
  @quot.lift G (G %. H) (G /. H) (λ g, quot.mk (G%.H) g⁻¹) 
  (λ a b, 
  begin
    intro h, simp, 
    have t₁ : (G %. H) b⁻¹ a⁻¹, 
      cases h with h₁ a₁, cases a₁ with a₁ eq₁, 
      rw ← G.inv_involution a at eq₁, rw ← G.mul_gauche_div_gauche at eq₁, 
      rw G.mul_droite_div_droite at eq₁, 
      have : (H .% G) b⁻¹ a⁻¹,
        apply Exists.intro h₁, apply Exists.intro a₁, assumption,
      rw distingue_gde dH, assumption, 
    have : (G %. H) a⁻¹ b⁻¹, 
      exact rel_gauche_symm H b⁻¹ a⁻¹ t₁, 
    exact quot.sound this, 
  end
  )


lemma quot_of_mul_quot {G: groupe} {H: sous_groupe G} {dH : est_distingue H}
  : ∀ a b : G, mul_quotient_ dH (⟦a⟧@H) (⟦b⟧@H) = ⟦a*b⟧@H :=
begin
  intros, unfold mul_quotient_, unfold mul_partielle_gauche_quotient_, refl, 
end

lemma existe_repr_of_quot {G : groupe} {H : sous_groupe G}
  : ∀ X : (G/.H), ∃ x : G, X = (⟦x⟧@H) :=
begin
  have : ∀ a : G, ∃ x : G, (⟦a⟧@H) = (⟦x⟧@H), intro, apply Exists.intro a, refl,
  intro X, 
  exact quot.ind this X, 
end

def groupe_quotient {G : groupe} (H : sous_groupe G) [dH : est_distingue H] : groupe :=
{
 ens := G /. H,
 mul := mul_quotient_ dH,
 inv := inv_quotient_ dH,
 neutre := quot.mk (G %. H) 1,
 inv_gauche := 
 begin 
  intro X, -- On introduit un élément X du groupe quotient
  cases existe_repr_of_quot X with g hg, rw hg, -- On choisit un représentant 
  unfold inv_quotient_, -- L'inverse de ⟦g⟧ est défini comme ⟦g⁻¹⟧
  rw← G.inv_gauche' g, -- On remplace ⟦1⟧ par ⟦g⁻¹*g⟧
  rw← quot_of_mul_quot g⁻¹ g, -- On remplace ⟦g⁻¹*g⟧ par ⟦g⟧*⟦g⁻¹⟧ et c'est fini
 end,
 mul_assoc :=
 begin
  repeat {intro X, cases existe_repr_of_quot X,}, -- On introduit les 3 elems, et on choisit 3 représentants
  rw [h, h_1, h_2], -- On remplace les élements avec leur écriture en fonction des représentants
  repeat {rw quot_of_mul_quot,}, -- On utilise la règle : ⟦a⟧*⟦b⟧=⟦a*b⟧ plusieurs fois
  rw G.mul_assoc', -- Enfin, on applique l'associativité sur G
 end, 
 neutre_gauche :=
 begin
  intro X, 
  cases existe_repr_of_quot X with g hg, rw hg,
  rw quot_of_mul_quot,
  rw G.neutre_gauche', 
 end,
}


local notation G ` /* `:61 H:61 := @groupe_quotient G H _

instance ens_quot_to_groupe_quot {G : groupe } {H : sous_groupe G} [H ⊲ G] : has_coe (G/.H) (G/*H)
  := ⟨id⟩

def mor_quotient {G : groupe} (H : sous_groupe G) [dH: est_distingue H] : morphisme G (G/*H) :=
{
  mor := λ g, ⟦g⟧@H,
  resp_mul := @quot_of_mul_quot G H dH,
}

lemma mor_quotient_id {G : groupe} {H : sous_groupe G} [dH: est_distingue H]
  : ∀ a : G, mor_quotient H a = ⟦a⟧@H := λ a, rfl

lemma quot_of_mul_quot' {G : groupe} {H : sous_groupe G} [dH: est_distingue H]
  : ∀ a b : G, ( (⟦a⟧@H * ⟦b⟧@H) : G/*H ) = (⟦a*b⟧@H) := @quot_of_mul_quot G H dH
lemma quot_of_inv_quot' {G : groupe} {H : sous_groupe G} [dH : est_distingue H]
  : ∀ a : G, ((⟦a⟧@H)⁻¹ : G/*H) = ⟦a⁻¹⟧@H :=
  by{intro, rw [←mor_quotient_id, ← mor_quotient_id, mor_inv_inv_mor]}
lemma one_quot_is_class_one {G : groupe} {H : sous_groupe G} [dH: est_distingue H]
  : (1: G/*H) = ⟦1⟧@H := rfl

lemma class_xh_is_x {G : groupe} {H : sous_groupe G} [dH: est_distingue H]
  (a : G) (h : H) : (⟦a*h⟧@H) = (⟦a⟧@H) :=
begin
  apply quot.sound, apply rel_gauche_symm, 
  existsi h.val, existsi h.property, refl, 
end

lemma repr_quot_one_in {G : groupe} (H : sous_groupe G) [dH: est_distingue H]
  : (repr_quot (1:G/*H)).val ∈ H :=
begin
  have p := (repr_quot (1:G/*H)).property,
  rw one_quot_is_class_one at p ⊢,
  have p₂ := quot_gauche_exact _ _ p,
  cases p₂ with h tmp, cases tmp with h_H ph,
  rw [G.mul_droite_all _ _ h⁻¹, mul_assoc', neutre_gauche', inv_droite, neutre_droite] at ph,
  rw ←ph,
  exact H.inv_stab _ h_H,
end

lemma class_one_iff {G : groupe} (H : sous_groupe G) [dH: est_distingue H] (a : G)
  : (⟦a⟧@H) = (1:G/*H) ↔ a ∈ H :=
begin
  split; intro p,
  rw one_quot_is_class_one at p, have p₂ := quot_gauche_exact _ _ p,
  cases p₂ with h tmp, cases tmp with h_H ph,
  rw (G.inv_unique ph.symm),
  exact H.inv_stab _ h_H,
  apply quot.sound, existsi a⁻¹, existsi H.inv_stab _ p, rw inv_droite, 
end
section

lemma mor_quotient_surj {G : groupe} {H : sous_groupe G} [dH : est_distingue H]
  : function.surjective (mor_quotient H) :=
begin
  intro b, existsi (repr_quot b).val,
  exact (repr_quot b).property,
end


-- Pour définir l'ordre, (∃ n : ℕ, x^(n:ℤ) = 1) n'est pas une proposition décidable en général
-- Il faut donc utiliser le module classical pour que toutes les propositions soient décidables
open classical
local attribute [instance, priority 10] prop_decidable

class ordre_fini {G : groupe} (x : G) : Prop := (h : (∃ n : ℕ, n≠0 ∧ x^(n:ℤ) = 1))

/-
On définit l'ordre d'un élément comme étant égal à :
  - Le plus petit n ∈ N* qui vérifie x^n = 1 si un tel n existe
  - 1 sinon
Cette définition n'est jamais à utiliser directement, et le lemme qui
vient après est celui qui nous permettra de travailler avec les ordres.
-/
noncomputable def ordre {G : groupe} (x : G) : ℕ :=
  if h : ordre_fini x then nat.find h.h else 0


lemma carac_ordre {G : groupe} (x : G) 
  : (x ^ (ordre x) = 1 ∧ ∀ k : ℕ, k ≠ 0 ∧ k < ordre x → x^k ≠ 1) :=
begin
  by_cases (ordre_fini x),
  { -- ==>
    have h₁ : (ordre x = nat.find h.h),
      unfold ordre, 
      exact simp_dite h,
    split,
    have h₂ := nat.find_spec h.h, rw  [←coe_pow_nat, ← h₁] at h₂, exact h₂.2, 
    intros k hk, cases hk with hk1 hk2,
    intro ha,
    rw h₁ at hk2,
    have h₂ := (@nat.find_min _ _ h.h k) hk2,
    simp at h₂,
    rw ← coe_pow_nat at h₂,
    exact h₂ ⟨hk1, ha⟩, 
  },
  { -- <==
    have h₁ : (ordre x = 0),
      unfold ordre,
      exact simp_dite_neg h,
    rw h₁,
    split,
      rw pow_zero_eq_one,
      intros k hk1,
      exfalso,
      exact nat.not_lt_zero k hk1.2,
  }
end

lemma ordre_fini_est_non_nul {G : groupe} {x : G} (h : ordre_fini x) : ordre x ≠ 0 :=
begin
  intro h₂, 
  have h₃ : (ordre x = nat.find h.h) := by {unfold ordre, exact simp_dite h},
  rw h₂ at h₃,
  have h₄ := (nat.find_spec h.h),
  exact h₄.1 h₃.symm, 
end

lemma ordre_fini_est_pos {G : groupe} {x : G} (h : ordre_fini x) : ordre x > 0 :=
  nat.lt_of_le_and_ne (nat.zero_le _) (ordre_fini_est_non_nul h).symm

class singleton_generateur {G : groupe} (x : G) : Prop :=
  (h : @sous_groupe_engendre G {x} = set.univ)

def est_cyclique (G : groupe ) := 
  ∃ x : G, singleton_generateur x

lemma x_pow_k_dans_engendre_x {G : groupe} {x : G}
  : ∀ k : ℤ, x ^ k ∈ sous_groupe_engendre ({x}:set G) :=
begin
  intros k,
  unfold sous_groupe_engendre,
  intro A,
  have h : x ∈ A.val, exact A.property.2 x rfl,
  simp,
  exact @x_pow_in_sous_groupe _ _ _ A.property.1 h k,
end


lemma engendre_singleton {G : groupe} (x : G) : 
  @sous_groupe_engendre G {x} = {y | ∃ k : ℤ, y = x^k}:=
  begin
    apply funext, 
    intro g, 
    apply propext, 
    split, 
    { --  Sens 1 : <x> ⊆ {x^k, k ∈ ℤ}  
      intro h, 
      rw engendre₂_est_engendre at h, 
      unfold sous_groupe_engendre₂ at h, simp at h, 
      cases h with L hL,
      revert g, 
      induction L with e L rL,
      {
        intros g hL, 
        unfold prod_all at hL,
        apply Exists.intro (0 : ℤ),
        rw [hL, ← int.coe_nat_zero, ← coe_pow_nat, pow_zero_eq_one],
      },
      {
        intros g hL,
        unfold prod_all at hL,
        have h₀ := rL (prod_all L (λ (a : {x_1 // ({x}:set G) x_1} × bool), ite (a.snd = tt) a.fst.val (a.fst.val)⁻¹)) rfl,
        cases h₀ with k hk,
        have h₁ : e.fst.val = x :=  e.fst.property, 
        cases e.snd,
        {
          simp at hL, have : (∀ a b, G.mul a b = a*b) := by{intros a b, refl}, rw this at hL,
          rw hk at hL, rw [hL, h₁],
          apply Exists.intro (k-1),
          rw [← pow_minus_one_eq_inv, pow_mul_pow], 
          rw int.add_comm, rw int.sub_eq_add_neg,
        },
        {
          simp at hL, have : (∀ a b, G.mul a b = a*b) := by{intros a b, refl}, rw this at hL,
          rw hk at hL, rw [hL, h₁],
          apply Exists.intro (k+1),
          apply eq.symm,
          exact mul_left_pow x, 
        }
      }
    },
    { -- Sens 2 : {x^k | k∈ℤ } ⊆ <x>
      intro h,
      cases h with k hk,
      rw hk,
      exact x_pow_k_dans_engendre_x _,
    }
  end

lemma pow_eq_pow_mod_ordre {G : groupe} {x : G} (h : ordre_fini x)
  : ∀ k : ℤ, x^k = x^(k%ordre(x)) :=
begin
  intro,
  have h₂ := int_mod_add_div k (ordre x),
  conv {to_lhs, rw h₂},
  rw ← pow_mul_pow,
  rw [mul_droite_div_droite, inv_droite],
  rw int.mul_comm,
  rw ← pow_pow,
  rw ← coe_pow_nat,
  rw (carac_ordre x).1,
  rw one_pow_eq_one,
end

lemma engendre_singleton_ordre_fini {G : groupe} (x : G) (h : ordre_fini x) 
  : @sous_groupe_engendre G {x} = {y | ∃ k : ℤ, (k ≥ 0) ∧ (k < ordre x) ∧ (y = x^k)} :=
begin
  rw engendre_singleton,
  apply funext, intro g, apply propext, split,
  { -- ⊆ 
    intro h₂, cases h₂ with k hk,
    rw (pow_eq_pow_mod_ordre h) k at hk,
    apply Exists.intro (k % (ordre x)),
    rw ← and.assoc, split,
      exact (int_mod_domaine k (ordre x) (ordre_fini_est_pos h)).symm,
      exact hk,
  },
  { -- ⊃
    intro h₂, cases h₂ with k hk,
    apply Exists.intro k,
    exact hk.2.2
  }
end

lemma carac_engendre_singleton_ordre_fini {G : groupe} {x : G} (h : ordre_fini x)
  : ∀ g : G, g ∈ (@sous_groupe_engendre G {x}) ↔ ∃ k : ℤ, (k ≥ 0) ∧ (k < ordre x) ∧ (g = x^k) :=
begin
  intro, rw engendre_singleton_ordre_fini x h, split,
    intro h, exact h,
    intro h, exact h,
end

lemma unicite_puissance_ordre_fini {G : groupe} {x : G} (h : ordre_fini x)
  : ∀ k k' : ℕ, k < ordre x → k' < ordre x → x^k = x^k' → k = k' :=
begin
  have both : ∀ k k' : ℕ, k < ordre x → k' < ordre x → x^k = x^k' → (k:ℤ) ≤ ↑k' → k = k', 
    intros k' k hk' hk h₁ h₄,
    rw [G.mul_droite_all _ _ (x^(-(int.of_nat k')))] at h₁,
    rw [coe_pow_nat, pow_mul_pow, int.coe_nat_eq,int.add_right_neg] at h₁,
    rw [← int.coe_nat_zero,  ← coe_pow_nat, pow_zero_eq_one] at h₁,
    rw [coe_pow_nat, pow_mul_pow] at h₁,
    rw [← int.sub_eq_add_neg, ←int.coe_nat_eq] at h₁,
    have h₂ := int.sub_le_sub h₄ (int.le_refl ↑k'), 
    rw [int.sub_eq_add_neg, int.add_right_neg] at h₂,
    rw ← int.coe_nat_lt_coe_nat_iff at hk, 
    have h₅ := int.sub_le_sub hk (int.coe_zero_le k'),
    rw [int.add_comm, int.add_sub_assoc, int.add_comm] at h₅,
    have h₆ : ↑k - ↑k' < ((ordre x):ℤ) - 0,
      exact h₅,
    have why : ∀ z : ℤ, z - 0 = z, intro, rw [int.sub_eq_add_neg, int.neg_zero, int.add_zero],
    rw (why _) at h₅,
    rw [int.coe_nat_le_coe_nat_iff] at h₄,
    have h₆ := int.lt_of_add_lt_add_right (int.lt_add_one_of_le h₅),
    rw [←int.coe_nat_sub h₄, int.coe_nat_lt_coe_nat_iff] at h₆,
    rw [←int.coe_nat_sub h₄, ←int.coe_nat_zero, int.coe_nat_le_coe_nat_iff] at h₂,
    have h₇ := (carac_ordre x).2 (k-k'),
    by_cases h₈ : (k-k') = 0,
      rw nat.sub_eq_zero_iff_le at h₈, exact nat.le_antisymm h₄ h₈,
      exfalso,
      rw [←int.coe_nat_sub h₄] at h₁, 
      exact h₇ ⟨h₈, h₆⟩ h₁.symm,
  intros k k' hk hk' h₁, 
  by_cases h₄: (k:ℤ) ≤ ↑k',
    {exact both k k' hk hk' h₁ h₄},
    {
      rw int.coe_nat_le_coe_nat_iff at h₄,
      have h₅ := (nat.lt_iff_le_not_le.1 (not_le.1 h₄)).1,
      rw ← int.coe_nat_le_coe_nat_iff at h₅, 
      apply eq.symm,
      exact both k' k hk' hk h₁.symm h₅,
    }


end

noncomputable def bijection_engendre_ordre_fini_nat {G : groupe} (x : G) [h : ordre_fini x]
  : bijection {g // g ∈ @sous_groupe_engendre G {x}} (fin (ordre x)) :=
{
  val := λ g, 
    let f_g := choose ((carac_engendre_singleton_ordre_fini h g.val).1 g.property) in
    ⟨int.nat_abs f_g.val, 
      begin
        have h₁ := int.eq_coe_of_zero_le f_g.property.1, cases h₁ with n h₁,
        have h₂ := f_g.property.2.1,
        rw h₁ at *,
        rw int.coe_nat_lt_coe_nat_iff at h₂, 
        rw int.nat_abs_of_nat,
        exact h₂,
      end
    ⟩,
  property := ⟨
    begin
      intro, intro, 
      simp,
      intro h₂,
      have h₃ := fin.mk.inj h₂,
      have h_a₁ : ∃ (k : ℤ), k ≥ 0 ∧ k < ↑(ordre x) ∧ a₁.val = x ^ k
        := (carac_engendre_singleton_ordre_fini h a₁.val).1 a₁.property,
      have h_a₂ : ∃ (k : ℤ), k ≥ 0 ∧ k < ↑(ordre x) ∧ a₂.val = x ^ k
        := (carac_engendre_singleton_ordre_fini h a₂.val).1 a₂.property,
      have h₄ : (choose h_a₁).val.nat_abs = (choose h_a₂).val.nat_abs, exact h₃,
      have p_a₁ := prop_of_choose h_a₁,
      have p_a₂ := prop_of_choose h_a₂,
      rw ← int.coe_nat_eq_coe_nat_iff at h₄,
      rw ← int.eq_nat_abs_of_zero_le p_a₁.1 at h₄,
      rw ← int.eq_nat_abs_of_zero_le p_a₂.1 at h₄,
      apply subtype.eq,
      rw [p_a₁.2.2, p_a₂.2.2],
      rw h₄,
    end,
    begin
      intro, simp,
      let g := x ^ (b.val),
      have hg : g ∈ sous_groupe_engendre ({x}:set G) := x_pow_k_dans_engendre_x b.val,
      let gg : {g' // g' ∈ sous_groupe_engendre ({x}:set G)} := ⟨g, hg⟩,  
      apply Exists.intro gg,
      apply fin.eq_of_veq, simp,
      have h₁ := (carac_engendre_singleton_ordre_fini h gg.val).1 gg.property,
      have p_gg := prop_of_choose h₁,
      rw ← int.coe_nat_eq_coe_nat_iff,
      have h₂ : gg.val = x^b.val := rfl, rw p_gg.2.2 at h₂,
      rw [int.eq_nat_abs_of_zero_le p_gg.1] at h₂,
      have lt₁ := p_gg.2.1, rw int.eq_nat_abs_of_zero_le p_gg.1 at lt₁,
      have lt₂ := b.property,
      rw int.coe_nat_lt_coe_nat_iff at lt₁,
      rw ←coe_pow_nat at h₂,
      rw int.coe_nat_eq_coe_nat_iff,
      have h₀ : gg.val = x^b.val, refl, 
      exact unicite_puissance_ordre_fini h _ _ lt₁ lt₂ h₂, 
    end
  ⟩
}

def bijection_cyclique_engendre {G : groupe} (x : G)
  [h : ordre_fini x] [h₂ : singleton_generateur x]
  : bijection G {g // g ∈ sous_groupe_engendre ({x}:set G)} :=
by {rw h₂.h, exact bij_univ_subtype G}

noncomputable def bijection_cyclique_fini_nat {G : groupe} (x : G)
  [h : ordre_fini x] [h₂ : singleton_generateur x]
  : bijection G (fin (ordre x)) :=
let B := bijection_engendre_ordre_fini_nat x in
let Id := bijection_cyclique_engendre x in
{
  val := B.val ∘ Id.val,
  property := function.bijective.comp B.property Id.property
}

@[instance]
noncomputable def engendre_fini_de_ordre_fini {G : groupe} {x : G} 
  [h : ordre_fini x] : est_fini {g // g ∈ @sous_groupe_engendre G {x}} :=
{
  majorant := ordre x,
  f := (bijection_engendre_ordre_fini_nat x).val,
  f_inj := (bijection_engendre_ordre_fini_nat x).property.1
}


@[instance]
noncomputable def cyclique_fini_de_ordre_fini {G : groupe} {x : G} 
  [h : ordre_fini x] [h₁ : singleton_generateur x] : est_fini G :=
  @fini_bij_fini {g // g ∈ @sous_groupe_engendre G {x}} _ G
    (λ g, ⟨g, by { unfreezingI{cases h₁ with h₁}, rw h₁, apply true.intro}⟩)
    begin {intro, intro, simp, intro aa, exact aa} end


--set_option trace.class_instances true 

lemma card_engendre_ordre_fini {G : groupe} {x : G} [h₂ : ordre_fini x]
  : cardinal {g // g ∈ @sous_groupe_engendre G {x}} = ordre x :=
begin
  apply card_proof1,
  exact bijection_engendre_ordre_fini_nat x,
end

lemma card_groupe_cyclique_fini {G : groupe} {x : G}
  [h₂ : ordre_fini x] [h₁ : singleton_generateur x]
  : cardinal G = ordre x :=
begin
  apply card_proof1,
  exact (bijection_cyclique_fini_nat x),
end


end
/-******************************Fin Définitions et coercions de base *****************************-/





def est_isomorphisme {G H : groupe} (f : G  →* H) : Prop :=
  ∃ (g : H  →* G), function.left_inverse g f ∧ function.right_inverse g f

lemma carac_est_isomorphisme {G H : groupe} (f : G  →* H)
  : est_isomorphisme f ↔ function.bijective f :=
begin 
  split,
  { -- isomorphisme → bijectif
    intro h, cases h with g hg,
    exact ⟨function.left_inverse.injective hg.1, function.right_inverse.surjective hg.2⟩, 
  },
  { -- bijectif → isomorphisme
    intro h,
    let f_bij_inv : bijection_inv G H := bijection_inv_of_bijection ⟨f, h⟩,
    let g := f_bij_inv.f_inv,
    have inv_resp_mul : ∀ a b : H, g (a*b) = g a * g b,
      intros, 
      apply h.1,
      rw mor_resp_mul,
      have h₁ := f_bij_inv.inv_droite,
        have h₂ : f_bij_inv.f = f, refl, rw h₂ at h₁,
      repeat {rw h₁},
      apply Exists.intro (⟨g, inv_resp_mul⟩ : H  →* G),
      exact ⟨f_bij_inv.inv_gauche, f_bij_inv.inv_droite⟩, 
  }
end


def sont_isomorphes (G G' : groupe) := ∃ f : G  →* G', est_isomorphisme f
local notation G `≋`:40 G' := sont_isomorphes G G'

@[symm] lemma sont_isomorphes_symm {G G' : groupe} : (G ≋ G') ↔ (G' ≋ G) :=
begin
  split; intro x;
  cases x with f pf; cases pf with g pfg; 
  existsi [g, f];
  exact ⟨pfg.2, pfg.1⟩,
end

@[trans] lemma sont_isomorphes_trans {G H K : groupe} : (G≋H) → (H≋K) → (G≋K) :=
begin
  intros gh hk,
  cases gh with f₁ t, cases t with g₁ t, cases t with pf₁ pg₁,  
  cases hk with f₂ t, cases t with g₂ t, cases t with pf₂ pg₂, 
  existsi [(f₂ ∘₁ f₁), (g₁ ∘₁ g₂)],
  split; intro p;
  repeat{rw [comp_mor_fun_eq, function.comp_app]},
    rw [pf₂, pf₁],
    rw [pg₁, pg₂],
end

lemma comp_isomorphisme {G H K : groupe} (g : H  →* K) (f : G  →* H) 
  (fI : est_isomorphisme f) (gI : est_isomorphisme g) : est_isomorphisme (g∘₁f) :=
  by {rw carac_est_isomorphisme at *, rw comp_mor_fun_eq, exact function.bijective.comp gI fI,}

def End (G : groupe) := G  →* G
def Aut (G : groupe) := {f : G  →* G // est_isomorphisme f}

def aut_int_fun {G : groupe} (g : G) (h : G) : G := g*h*g⁻¹
def aut_int {G: groupe} (g : G) : G  →* G :=
  { mor:= aut_int_fun g,
    resp_mul := 
    begin
    intro a,
    intro b, unfold aut_int_fun,
    rw ← mul_assoc' G (g*a*g⁻¹) (g * b) g⁻¹,
    rw ←  mul_assoc' G (g*a*g⁻¹) g  b,
    rw mul_assoc' G (g*a) g⁻¹ g,
    rw inv_gauche',
    rw neutre_droite,
    rw mul_assoc' G g a b,    
    end
  }
    

lemma aut_int_est_iso {G: groupe} (g : G) : est_isomorphisme (aut_int g) :=
begin
  apply Exists.intro (aut_int g⁻¹),
  split; intro; unfold aut_int; repeat {rw mor_fun_eq}; simp; unfold aut_int_fun,
  {
    rw [inv_involution, ← G.mul_assoc' g⁻¹, ← G.mul_assoc' g⁻¹, G.inv_gauche'],
    rw [G.neutre_gauche', G.mul_assoc', G.inv_gauche', G.neutre_droite],
  }, 
  {
    rw [inv_involution, ← G.mul_assoc' g, ← G.mul_assoc' g, G.inv_droite],
    rw [G.neutre_gauche', G.mul_assoc', G.inv_droite, G.neutre_droite],
  }
end

def Int (G: groupe) := {f // ∃ g:G , f = aut_int g } 


def im_recip {G H : groupe} (f : G  →* H) (B: set H) :=
  im_recip (f : G→H) B

def ens_image {G H : groupe} (f : G  →* H) (A: set G) :=
  im_dir (f : G→H) A

def ker {G H : groupe} (f : G  →* H) : set G :=
  {a : G.ens | f a = 1}

def im {G H : groupe} (f : G  →* H) : set H :=
  {b : H | ∃ a : G, f a = b }

-- ↓ Utile pour pruver qu'un élément appartient à l'image
lemma im_point_in_im {G H : groupe} (f : G  →* H) (x : G)
  : f x ∈ im f := by {apply Exists.intro x, refl}
lemma im_point_in_im_ss_ens {G H : groupe} (f : G  →* H) (A : set G) (x ∈ A)
  : f x ∈ (ens_image f A) := by {existsi x, existsi H, refl,}
-- ↓ Utile pour prouver qu'un élément appartient au noyeau
lemma im_one_in_ker {G H : groupe} (f : G  →* H) (x : G)
  : (f x = 1) ↔ (x ∈ ker f) := iff.intro id id
lemma in_ens_image {G H : groupe} (f : G  →* H) (B : set H) (x : G)
  : (f x ∈ B) = (x ∈ im_recip f B) := rfl 

lemma ker_est_preim_neutre {G H : groupe} (f : G  →* H)
  : ker f = im_recip f {1} := 
  by {rw ←set_eq, intro, split; intro p; rw [←im_one_in_ker, ←in_singleton (1:H), in_ens_image] at *; exact p,}
lemma im_est_im_univ {G H : groupe} (f : G  →* H)
  : im f = ens_image f set.univ :=
  by {rw ←set_eq, intro, unfold ens_image, unfold im_dir, unfold im, 
      split; intro p; cases p with a₁ ha; existsi a₁, existsi (in_univ a₁), exact ha,
      cases ha with _ p, exact p,}

@[instance] lemma ker_est_sous_groupe {G H : groupe} (f : G  →* H)
  : est_sous_groupe (ker f) :=
begin 
  split,
  { -- stabilité de l'inverse
    intros a h, rw ←im_one_in_ker at *,
    rw mor_inv_inv_mor,
    rw h,
    rw [H.mul_droite_all _ _ 1, inv_gauche', neutre_gauche'],
  },
  {
    intros a ha b hb, 
    rw ←im_one_in_ker at *, 
    rw [mor_resp_mul, ha, hb, neutre_droite], 
  },
  exact mor_neutre_est_neutre,
end

@[instance] lemma im_ss_groupe_est_ss_groupe {G H : groupe} (f : G  →* H) (G' : sous_groupe G)
  : est_sous_groupe (ens_image f G') := 
begin
  split, {
    intros a tmp, cases tmp with pre_a tmp, cases tmp with a_in a_eq, 
    apply Exists.intro pre_a⁻¹, apply Exists.intro (G'.inv_stab _ a_in),
    rw mor_inv_inv_mor,
    rw eq_of_inv_eq, exact a_eq,
  }, {
    intros a tmp_a b tmp_b,
    cases tmp_a with pre_a tmp, cases tmp with a_in a_eq,
    cases tmp_b with pre_b tmp, cases tmp with b_in b_eq,
    apply Exists.intro (pre_a*pre_b), apply Exists.intro (G'.mul_stab _ a_in _ b_in),
    rw [mor_resp_mul, a_eq, b_eq],
  }, {
    apply Exists.intro (1:G), apply exists.intro G'.contient_neutre,
    exact mor_neutre_est_neutre,
  }
end

@[instance] lemma im_est_ss_groupe {G H : groupe} (f : G  →* H) 
  : est_sous_groupe (im f) :=
begin
  rw im_est_im_univ, 
  apply im_ss_groupe_est_ss_groupe f (↩set.univ),
end

@[instance] lemma preim_ss_groupe_est_ss_groupe {G H : groupe} (f : G  →* H) (H' : sous_groupe H)
  : est_sous_groupe (im_recip f H') :=
begin
  split, {
    intros a ha, rw ←in_ens_image at *,
    rw mor_inv_inv_mor,
    exact H'.inv_stab _ ha, 
  }, {
    intros a ha b hb, rw ←in_ens_image at *,
    rw mor_resp_mul,
    exact H'.mul_stab _ ha _ hb,
  }, {
    rw [←in_ens_image, mor_neutre_est_neutre], exact H'.contient_neutre,
  }
end

lemma carac_mor_inj {G H : groupe} (f : G  →* H) 
  : function.injective f ↔ ker f = {(1:G)} :=
begin
  split, {
    intro f_inj, rw ←set_eq, intro, split;intro h, 
    rw ←im_one_in_ker at h, rw in_singleton, 
    rw ← @mor_neutre_est_neutre _ _ f at h,
    exact f_inj h,
    rw in_singleton at h, rw ←im_one_in_ker, rw h, 
    exact mor_neutre_est_neutre,
  }, {
    intro h, intros a₁ a₂ eq,
    rw mul_right_inv_eq_one_of_eq at *,
    rw [←mor_inv_inv_mor, ←mor_resp_mul] at eq,
    rw [im_one_in_ker, h] at eq,
    rw in_singleton at eq, 
    exact eq,
  }
end

lemma carac_mor_surj {G H : groupe} (f: G  →* H)
  : function.surjective f ↔ im f = set.univ :=
begin
  split;intro p, {
    rw ←set_eq, intro a, split; intro p₂, exact in_univ _,
    cases (p a), existsi w, exact h, 
  }, {
    intro, have h₀ : b∈set.univ := in_univ _, rw ←p at h₀,
    cases h₀ with a pa,
    existsi a, exact pa,  
  }
end

theorem ker_comp_eq_inv_ker {G H K: groupe} (g : H  →* K) (f : G  →* H)
  : ker (g ∘₁ f) = im_recip f (ker g) := by {refl} 
-- ↑ Par définition, x ∈ ker (g ∘ f) est égal à x ∈ f⁻¹ (ker g). Lean sait faire seul c: 

theorem im_comp_eq_im_im {G H K: groupe} (f : G  →* H) (g : H  →* K) 
  : im (g ∘₁ f) = ens_image g (im f) :=
begin
  rw ←set_eq, intro a, split; intro h,
    { -- im (g ∘ f) ⊆ g (im f)
      cases h with x hx, unfold ens_image,
      apply Exists.intro (f x),
      apply Exists.intro (im_point_in_im f x), rw comp_mor_fun_eq g f at hx, exact hx,
    },
    { -- g (im f) ⊆ im (g ∘ f)
      cases h with x hx, cases hx with h₁ h₂,
      cases h₁ with y hy,
      rw [← hy, ←function.comp_app (g:H→K), ← comp_mor_fun_eq] at h₂,
      rw ← h₂,
      exact im_point_in_im _ y,
    }
end

@[instance] lemma preim_distingue_est_distingue {G H : groupe} (f : G  →* H) {K : sous_groupe H}
  (dK : K ⊲ H) : (↩(im_recip f K)) ⊲ G :=
begin
  rw carac_est_distingue at dK ⊢, 
  intros h ph g, rw mem_ss_groupe_simp at ph ⊢,
  rw [sous_groupe_de_est_sous_groupe_id, ←in_ens_image] at ph ⊢,
  repeat {rw mor_resp_mul}, rw mor_inv_inv_mor,
  exact dK _ ph (f g), 
end


@[instance] lemma ker_est_distingue {G H : groupe} (f : G  →* H) : ((↩(ker f)) ⊲ G) :=
begin
  simp only [ker_est_preim_neutre f],
  apply preim_distingue_est_distingue f (triv_est_distingue H), 
end

def mor_vu_dans_im {G H : groupe} (f : G  →* H) : morphisme G ↩(im f) :=
{
  mor := λ g, ⟨f g, im_point_in_im f g⟩,
  resp_mul := λ g g',
  begin
    apply subtype.eq, rw coe_mul_sous_groupe,
    have why : ∀ (α : Type*) (p : α → Prop) (a : α) (b : p a), 
      (subtype.mk a b).val = a, intros, refl, 
    repeat {rw why _  (λ a, a ∈ (↩im f).sous_ens)},
    exact mor_resp_mul _ _,
  end,
}

local notation f`↓`:51 := mor_vu_dans_im f

lemma mor_vu_dans_im_id {G H : groupe} (f : G  →* H) (a : G) 
  : ((f↓) a).val = f a := rfl


@[instance] lemma im_distingue_est_distingue_dans_im {G H : groupe} (f : G  →* H)
  {A : sous_groupe G} (dA : A ⊲ G) : (↩(ens_image (f↓) A)) ⊲ (↩(im f)) := 
begin
  rw carac_est_distingue at dA ⊢,
  intros h ph g,
  rw [mem_ss_groupe_simp, sous_groupe_de_est_sous_groupe_id] at ph ⊢,
  cases ph with h' tmp, cases tmp with h'_A ph',
  rw ← ph', 
  cases g.property with rg prg, rw ←mor_vu_dans_im_id at prg,
  have p₂ := subtype.eq prg,
  rw ← p₂,
  rw [←mor_resp_mul, ←mor_inv_inv_mor, ←mor_resp_mul], 
  apply im_point_in_im_ss_ens,
  exact dA h' h'_A rg,
end


lemma univ_isomorphe_groupe (G : groupe) : G ≋ (↩(@set.univ G)) :=
begin
  existsi (⟨λ g, ⟨g, true.intro⟩, 
           by{intros, apply subtype.eq, rw [coe_mul_sous_groupe]}⟩ 
           : morphisme G (↩(@set.univ G))),
  rw carac_est_isomorphisme, split,
  intros a a' aa, have aa' := app_eq (λ x:↩(@set.univ G), x.val) aa, exact aa', 
  intro b, existsi b.val, apply subtype.eq, refl,
end

lemma im_surj_isomorphe_arrivee {G G' : groupe} (f : G  →* G') (fS : function.surjective f)
  : G' ≋ (↩im f) :=
begin
  have h₀ := (carac_mor_surj _).1 fS, simp [h₀],
  exact univ_isomorphe_groupe _, 
end

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

lemma centre_est_distingue (G : groupe) : (↩(centre G)) ⊲ G :=
begin
  rw carac_est_distingue,
  intros h h_comm g,
  rw [mem_ss_groupe_simp, sous_groupe_de_est_sous_groupe_id] at h_comm ⊢,
  rw ←h_comm g,
  rw [mul_assoc',inv_droite,neutre_droite],
  exact h_comm,
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

noncomputable instance quot_fini_de_gr_fini {G : groupe} {H : sous_groupe G} [fG : est_fini G] : est_fini (G /. H) :=
{
  majorant := fG.majorant,
  f := λ X, fG.f (repr_quot X).val,
  f_inj :=
  begin
    intros A A' AA, simp at AA,
    have p := fG.f_inj AA,
    rw [←(repr_quot A).property, ←(repr_quot A').property],
    rw p, 
  end
}


noncomputable def fun_gr_prod_ss_gr_quot {G : groupe} {H : sous_groupe G} (U : H × (G/.H)) : G
  := repr_quot(U.2)*U.1

/-
Théorème 1.37 du cours
La preuve ici consiste à exhiber une bijection entre G et (H × G/H):
  - On se munit de repr_quot : G/H → G qui nous donne un représentant arbitraire pour chaque classe.
  - On montre que la fonction qui à (h, X) repr_quot(X)*h est une bijection
-/
theorem theoreme_de_lagrange {G : groupe} (H : sous_groupe G) [fG : est_fini G]
  : cardinal G = cardinal H * cardinal (G /. H) :=
begin 
  rw ← prod_of_cards, 
  apply eq_card_of_idempotents, apply bijection_comm,
  exact {
    val := fun_gr_prod_ss_gr_quot, 
    property :=
    begin
      split, { -- Preuve que c'est une injection
        -- On introduit (h, X) et (h', X') tq f(h, X) = f(h', X')
        intros a a',
        cases a with h X, cases a' with h' X',
        intro aa,
        unfold fun_gr_prod_ss_gr_quot at aa, 

        -- On montre que repr(X) et repr(X') sont équivalents et que donc X = X'
        have aa_equiv : (⟦repr_quot X⟧@H)= (⟦repr_quot X'⟧@H),
          apply quot.sound,
          apply rel_gauche_carac₂,
          exact aa, 
        repeat {rw class_of_repr_quot at aa_equiv},
        
        -- On montre que h = h'
        rw aa_equiv at *, 
        rw ←mul_gauche_all at aa, 
        simp at aa, rw eq_in_ss_groupe_iff_eq at aa,
        rw aa, 
      }, { -- Preuve que c'est une surjection
        intro, 
        let x := repr_quot(⟦b⟧@H),
        have p : rel_gauche_mod H x b,
          exact quot_gauche_exact _ _ x.property,
        cases p with h hp, cases hp with h_H ph,
        existsi (⟨⟨h, h_H⟩, ⟦b⟧@H⟩ : H × (G/.H)),
        
        have why : ∀ x y, fun_gr_prod_ss_gr_quot ⟨x, y⟩ = (repr_quot y)*x := λ x y, rfl, 
        rw why,

        conv {to_rhs, rw ph},
        have why₂ : ((⟨h, h_H⟩:H):G) = h := rfl, rw why₂,
      }
    end
  }
end

lemma card_ss_groupe_div_card_groupe {G : groupe} (H : sous_groupe G) [fG : est_fini G]
  : (cardinal H) ∣ (cardinal G) := Exists.intro (cardinal (G/.H)) (theoreme_de_lagrange H)



lemma mor_quot_ker_inj {G G' : groupe} {f : G  →* G'} (fI : function.injective f)
  : est_isomorphisme  (mor_quotient (↩ker f)) :=
begin
  rw carac_mor_inj at fI,
  rw carac_est_isomorphisme, split, { -- injectif
    intros a b ab, repeat{rw mor_quotient_id at ab},
    have ab' := quot_gauche_exact _ _ ab,
    cases ab' with k hk, cases hk with k_K hk,
    rw [sous_groupe_de_est_sous_groupe_id, fI, in_singleton] at k_K,
    rw [hk, k_K, neutre_droite],
  }, { --surjectif
    exact mor_quotient_surj,
  }
end

lemma iso_quot_ker_inj {G G' : groupe} {f : G  →* G'} (fI : function.injective f)
  : G ≋ G/*↩ker f := by{existsi (mor_quotient _), exact mor_quot_ker_inj fI,}

theorem theoreme_de_factorisation {G G': groupe} (f : G  →* G') (H : sous_groupe G)
  [dH : est_distingue H] (H_ker : ∀ x : H, f x = 1): ∃! f' : morphisme (G/*H) G', f = f' ∘₁ (mor_quotient H) :=
begin
  have f_resp_rel_gauche : ∀ a b : G, rel_gauche_mod H a b → f a = f b,
    intros a b pab,
    cases pab with h tmp, cases tmp with h_H p, 
    rw [G.mul_gauche_all _ _ a⁻¹, ←mul_assoc', inv_gauche',neutre_gauche'] at p,
    apply eq.symm,
    rw [mul_left_inv_eq_one_of_eq, ←mor_inv_inv_mor, ←mor_resp_mul],
    rw p,
    exact H_ker ⟨h, h_H⟩,
  let f' : (G/*H) → G' := (quot.lift f f_resp_rel_gauche),
  have f'_resp_mul : ∀ A B : (G/*H), f' (A*B) = f' A * f' B,
    intro A, apply quot.ind, intro b, revert A, apply quot.ind, intro a,
    repeat {rw ←mor_quotient_id}, rw ← mor_resp_mul, repeat {rw mor_quotient_id},
    have why: ∀ x, f' (⟦x⟧@H) = (quot.lift f f_resp_rel_gauche) (⟦x⟧@H), intro,refl,
    repeat{rw [why, quot_lift_id f dH]},
    exact f.resp_mul a b,
  apply exists_unique.intro (⟨f', f'_resp_mul⟩ : morphisme (G/*H) G'),
  { -- preuve que f = f' ∘ cl 
    rw morphisme_eq_iff, funext, 
    rw comp_mor_id,
    unfold mor_quotient,
  }, { -- preuve de l'unicite
    intros g pg,
    rw morphisme_eq_iff, funext,
    simp [mor_id],
    have p₀ : (⟦repr_quot x⟧@H) = x:= class_of_repr_quot x,
    rw ← p₀,
    conv {to_lhs, rw [←mor_quotient_id, mor_id, ← comp_mor_id, ←pg]},
  }
end

def plongeon {G : groupe} (H : sous_groupe G) : H  →* G := ⟨λ h, h.val, coe_mul_sous_groupe⟩
lemma plongeon_id {G : groupe} (H : sous_groupe G) (a : H) : plongeon H a = (a : G):= rfl

theorem pre_theoreme_isomorphisme₁ {G G' : groupe} (f : G  →* G')
  : ∃! f' : morphisme (G/*(↩ker f)) ↩im f, f = plongeon _ ∘₁ f' ∘₁ (mor_quotient ↩(ker f)) :=
begin
  
  -- On prend la fonction dont l'existence est démontrée par le théorème de factorisation 
  have p₁ := theoreme_de_factorisation (f↓) (↩(ker (f))) 
    (by {intro, apply subtype.eq,rw mor_vu_dans_im_id, exact x.property,}),
  cases p₁ with f' tmp, cases tmp with pf' f'_unique, 
  existsi f',

  split;simp,
  { -- On montre qu'elle satisfait : f = i∘f'∘cl 
    rw morphisme_eq_iff at ⊢ pf', funext,
    rw ←mor_vu_dans_im_id,
    rw pf',
    refl,  
  }, { -- On montre l'unicité
    intros g pg, 
    have p₁ := f'_unique g, 
    rw morphisme_eq_iff at ⊢ pf' pg p₁,
    simp at p₁,
    apply p₁,
    rw morphisme_eq_iff, funext,
    apply subtype.eq,
    rw mor_vu_dans_im_id,
    rw pg,
    refl, 
  }
end


theorem theoreme_isomorphisme₁ {G G' : groupe} (f : G  →* G')
  : (G/*↩ker f) ≋ ↩im f :=
begin
  have p₁ := pre_theoreme_isomorphisme₁ f, 
  cases p₁ with f' tmp, cases tmp with p₁, 
  existsi f', 
  rw carac_est_isomorphisme,
  simp [morphisme_eq_iff₂, comp_mor_fun_eq] at p₁,
  split, { -- Injectif
    rw [carac_mor_inj, ←set_eq], simp only [in_singleton, ←im_one_in_ker],
    apply quot.ind, intro, 
    split;intro p, 
      have p₂ := app_eq (plongeon _) p,
      rw [←mor_quotient_id, ←p₁ a, plongeon_id, coe_sous_groupe, coe_one_sous_groupe] at p₂,
      rw im_one_in_ker at p₂,
      rw class_one_iff,
      exact p₂,
      rw [p, mor_neutre_est_neutre],
  }, { -- Surjectif 
    intro b, cases b.property with a fa_b,
    existsi ⟦a⟧@_,
    rw ←eq_in_ss_groupe_iff_eq, 
    rw [←plongeon_id, ←mor_quotient_id],
    rw [←p₁, fa_b, coe_sous_groupe], 
  }
end

lemma theoreme_isomorphisme₁_inj {G G' : groupe} {f : G  →* G'} (fI : function.injective f)
  : G ≋ ↩im f :=
begin
  have p₀ : G ≋ G/*↩ker f := iso_quot_ker_inj fI, 
  have p₁ : G/*↩ker f ≋ ↩im f := theoreme_isomorphisme₁ _, 
  exact sont_isomorphes_trans p₀ p₁,
end

lemma theoreme_isomorphisme₁_surj {G G' : groupe} {f : G  →* G'} (fS : function.surjective f)
  : G/*↩ker f ≋ G' :=
begin
  have p₀ :  G/*↩ker f ≋ ↩im f := theoreme_isomorphisme₁ _,
  have p₁ : ↩im f ≋ G' := sont_isomorphes_symm.1 (im_surj_isomorphe_arrivee _ fS),
  exact sont_isomorphes_trans p₀ p₁,
end


-- Définitions en rapport avec le théorème d'isomorphisme 2 : 
-- Pour H < G et K ⊲ G, on définit HK < G et on montre que K∩H ⊲ G
def ss_groupe_mul_ss_groupe {G : groupe} (H K : sous_groupe G)
  : set G :=  {x | ∃ (h∈H) (k∈K), x = h*k}
local notation H `*₀`:57 K:57 := ss_groupe_mul_ss_groupe H K
local notation H `⬝`:67 K:67 := (↩H*₀K)

@[instance] lemma ss_mul_distingue_est_sous_groupe {G : groupe} (H K : sous_groupe G)
  [est_distingue K] : est_sous_groupe (H*₀K) :=
begin
  have p₁ : (H*₀K) = im_recip (mor_quotient K) (ens_image (mor_quotient K) H),
    rw ←set_eq, intro, split; intro p, 
      { -- HK ⊆ cl⁻¹(cl(H)) 
        cases p with h tmp, cases tmp with h_H tmp,
        cases tmp with k tmp, cases tmp with k_K phk,   
        rw [←in_ens_image, mor_quotient_id],
        have p' := app_eq (@quot.mk G (G%.K)) phk,
        rw [p', coe_sous_groupe₂ k k_K, class_xh_is_x], 
        existsi [(h:G), h_H], 
        rw mor_quotient_id,
      }, { -- cl⁻¹(cl(H)) ⊆ HK 
        rw [←in_ens_image] at p,
        cases p with h tmp, cases tmp with h_H ph, 
        rw [mor_quotient_id, mor_quotient_id] at ph,
        have p₂ := quot_gauche_exact _ _ ph,
        cases p₂ with k tmp, cases tmp with k_K p,
        existsi [h, h_H, k, k_K], 
        exact p,
      },
  have p₂ := preim_ss_groupe_est_ss_groupe (mor_quotient K) (↩(ens_image (mor_quotient K) H)),
  rw sous_groupe_de_est_sous_groupe_id at p₂,
  rw ←p₁ at p₂,
  exact p₂,
end

@[instance] lemma H_inclus_HK {G : groupe} (H K : sous_groupe G)
  [est_distingue K] : H ⊆₁ (H⬝K) :=
begin
  split, intros h h_H, rw sous_groupe_de_est_sous_groupe_id,
  existsi [h, h_H, (1:G), K.contient_neutre], rw neutre_droite,
end

@[instance] lemma K_inclus_HK {G : groupe} (H K : sous_groupe G)
  [est_distingue K] : K ⊆₁ (H⬝K) :=
begin
  split, intros k k_K, rw sous_groupe_de_est_sous_groupe_id,
  existsi [(1:G), H.contient_neutre, k, k_K], rw neutre_gauche',
end

instance intersection_sous_groupes {G : groupe} : has_inter (sous_groupe G) := ⟨λ H K, ↩((H : set G)∩K)⟩ 

@[instance] lemma KiH_inclus_HK {G : groupe} (H K : sous_groupe G)
  [est_distingue K] : (K ∩ H) ⊆₁ (H⬝K) := by {split, intros a pa, exact (K_inclus_HK _ _).h _ pa.1}

@[instance] lemma KiH_inclus_H {G : groupe} (H K : sous_groupe G)
  [est_distingue K] : (K∩H) ⊆₁ H := by {split, intros g pg, exact pg.2}

-- Le morphisme naturel de H vers HK
def injection_H_HK {G : groupe} (H K : sous_groupe G) [est_distingue K] : morphisme H (H⬝K) :=
{
  mor := λ h, ⟨h.val, (H_inclus_HK _ _).h _ h.property⟩,
  resp_mul := begin
    intros, 
    apply subtype.eq,
    rw [@coe_mul_sous_groupe _ (H⬝K), coe_mul_sous_groupe],
  end
}

-- La suite p : H → HK → HK/K de la preuve du polycopié
def suite_comp_thm_iso₂ {G : groupe} (H K : sous_groupe G) [dK : est_distingue K]
  : morphisme H ((H⬝K) /* K↘(H⬝K))
  := (mor_quotient (K↘(↩H⬝K))) ∘₁ (injection_H_HK _ _)

lemma ker_suite_comp_thm_iso₂ {G : groupe} (H K : sous_groupe G) [dK : est_distingue K]
  : ((K∩H)↘H) = ↩(ker (suite_comp_thm_iso₂ H K)) :=
begin
  rw [sous_groupe_eq_iff, sous_groupe_down_ens, sous_groupe_de_est_sous_groupe_id],
  rw ←set_eq, intro h, split;intro p;
  rw ←im_one_in_ker at *;
  unfold suite_comp_thm_iso₂ at *; 
  rw [comp_mor_fun_eq, function.comp_app, mor_quotient_id, class_one_iff] at *,
    exact p.1,-- K∩H ⊆ ker p (Ex compli)
    exact ⟨p, h.property⟩, --ker p ⊆ K∩H
end

lemma im_suite_comp_thm_iso₂ {G : groupe} (H K : sous_groupe G) [dK : est_distingue K]
  : function.surjective (suite_comp_thm_iso₂ H K) :=
begin
  intro, cases (repr_quot b) with b_v p₁, cases b_v with b_v p₂,
  cases p₂ with h t, cases t with h_H t, cases t with k t, cases t with k_K phk, 
  existsi (⟨h,h_H⟩:H), 
  unfold suite_comp_thm_iso₂,  
  rw [comp_mor_fun_eq, function.comp_app, mor_quotient_id,←p₁],
  apply quot.sound,
  existsi (⟨⟨k, (K_inclus_HK _ _).h _ k_K⟩, k_K⟩: K↘(H⬝K)).val,
  existsi k_K,
  apply subtype.eq,
  exact phk,
end

@[instance] lemma K_inter_H_distingue_H {G : groupe} (H K : sous_groupe G)
  [dK : est_distingue K] : est_distingue ((K∩H)↘H) :=
begin
  have ker_p_distingue := ker_est_distingue (suite_comp_thm_iso₂ H K),
  rw ←ker_suite_comp_thm_iso₂ at ker_p_distingue, 
  exact ker_p_distingue,
end

theorem theoreme_isomorphisme₂ {G : groupe} (H K : sous_groupe G) [dK : est_distingue K]
  : H /* (K∩H)↘H ≋ (H⬝K) /* K↘(H⬝K) :=
begin
  have h₂ :  (↩ im (suite_comp_thm_iso₂ H K)) ≋ (((H⬝K))/*(K↘(H⬝K))),
    rw sont_isomorphes_symm,
    exact im_surj_isomorphe_arrivee (suite_comp_thm_iso₂ H K) (im_suite_comp_thm_iso₂ H K),
  have h₁ : H /* (K∩H)↘H ≋ ↩im (suite_comp_thm_iso₂ H K),
    simp only [ker_suite_comp_thm_iso₂ H K], 
    exact theoreme_isomorphisme₁ (suite_comp_thm_iso₂ H K),
  exact sont_isomorphes_trans h₁ h₂,
end

-- Classe permettant de plonger un groupe dans un autre en fournissant une injection canonique.
-- Cette classe est utile pour le troisième théorème d'isomorphisme: on voit dans celui-ci le 
-- quotient (G/K)/(H/K): 
--   -Dans le formalisme ZFC, cela ne pose pas de problème: on peut montrer 
--    que l'ensemble H/K des classes est bien un sous ensemble de l'ensemble G/K des classes,
--    et que leurs lois de multiplication respectives sont les mêmes, et que H/K ⊲ G/K
--   -Dans le formaliste de Lean, en définissant les quotients avec quot.mk, G/K et H/K sont deux
--    objets complétement distincts, et il faut alors indiquer à lean que H/K est considéré comme
--    un sous groupe de G/K avec l'injection naturelle : λ ⟦h:H⟧@K, ⟦h:G⟧@K
class injection_naturelle (G G': groupe) :=
  (mor : G  →* G')
  (mor_inj : function.injective mor)

-- Si G' injecte G par une injection i, le sous groupe représentant G' dans G est i
@[reducible] def sous_groupe_de_injection_naturelle  (G G' : groupe) [GiG' : injection_naturelle G G']
  : sous_groupe G' := (↩im GiG'.mor)

local notation G `↪`:60 G':60 := sous_groupe_de_injection_naturelle G G' 

lemma bijection_de_injection_naturelle (G G' : groupe) [i : injection_naturelle G G']
  : G ≋ G↪G' :=
begin
  have p₀ : G ≋ ↩im i.mor := theoreme_isomorphisme₁_inj i.mor_inj,
  unfold sous_groupe_de_injection_naturelle, 
  exact p₀, 
end

lemma sous_groupe_de_injection_naturelle_id (G G' : groupe) [i : injection_naturelle G G']
  : (G↪G') = ↩im i.mor := rfl 

-- Une reformulation du fait que H/K (vu comme un ensemble de classes) est inclus dans G/K
lemma double_quot_sub_quot {G : groupe} (H K : sous_groupe G) [HinK : K ⊆₁ H]
  {a b : H} (a_equiv_b : ⟦a⟧@(K↘H) = ⟦b⟧@(K↘H)) : ⟦a⟧@K = ⟦b⟧@K :=
begin
  have aeb := quot_gauche_exact _ _ a_equiv_b,
  cases aeb with k t, cases t with k_K pab,
  rw pab, 
  apply quot.sound,
  existsi [k.val, k_K],
  refl,
end

noncomputable def plongeon_HdK_GdK {G : groupe} {H K : sous_groupe G} [KinH : K ⊆₁ H] [dK : K⊲G]
  : morphisme (H/*(K↘H)) (G/*K) := 
{
  mor := λ a, ⟦(repr_quot a).val.val⟧@K,
  resp_mul := begin
    intros a b,
    rw quot_of_mul_quot', 
    rw ←coe_mul_sous_groupe,
    repeat{rw ←coe_sous_groupe},
    apply double_quot_sub_quot H K,
    rw (repr_quot ((a*b):H/*(K↘H))).property,
    rw ←quot_of_mul_quot',
    rw [(repr_quot a).property,(repr_quot b).property],
  end
}


lemma plongeon_HdK_GdK_id {G : groupe} (H K : sous_groupe G) [KinH : K ⊆₁ H] [dK : K⊲G]
  : ∀ a : H/*(K↘H), (plongeon_HdK_GdK a) = (⟦(repr_quot a).val.val⟧@K) := λa, rfl
lemma plongeon_HdK_GdK_id₂ {G : groupe} (H K : sous_groupe G) [KinH : K ⊆₁ H] [dK : K⊲G]
  : ∀ h : H, (plongeon_HdK_GdK ⟦h⟧@(K↘H)) = ⟦h.val⟧@K :=
begin
  intro, rw plongeon_HdK_GdK_id, apply quot.sound,
  have p₀ := (repr_quot ⟦h⟧@(K↘H)).property,
  have p₁ := quot_gauche_exact _ _ p₀,
  cases p₁ with k t, cases t with k_K pk,
  existsi k.val, existsi k_K, 
  rw ←coe_mul_sous_groupe,
  conv{to_lhs,rw pk},
end

lemma plongeon_HdK_GdK_im_distingue {G : groupe} (H K : sous_groupe G) [KinH : K ⊆₁ H] [dK : K⊲G] [dH : H⊲G]
  : est_distingue ↩im (@plongeon_HdK_GdK _ H K _ _) :=
begin
  rw carac_est_distingue, intros B ha,
  cases ha with A pA,
  rw ←(repr_quot A).property at pA,
  rw plongeon_HdK_GdK_id₂ at pA,
  apply quot.ind,
  intro g,
  rw [←pA, quot_of_mul_quot', quot_of_inv_quot',quot_of_mul_quot'],
  let ghg : H := ⟨g*(repr_quot A).val.val*g⁻¹, (carac_est_distingue H).1 dH _ (repr_quot A).val.property g⟩,
  have p₁ : ghg.val = g * (repr_quot A).val.val * g⁻¹ := rfl,
  rw ←p₁,
  rw ←plongeon_HdK_GdK_id₂,
  exact im_point_in_im _ _,
end

@[instance] noncomputable def injection_naturelle_HdK_GdK {G : groupe} (H K : sous_groupe G) [KinH : K ⊆₁ H] [dK : K⊲G]
  : injection_naturelle (H/*(K↘H)) (G/*K) := 
{
  mor := plongeon_HdK_GdK, -- On définit le morphisme naturel H/K → G/K 
  mor_inj := begin
    intros a b pab, 
    rw [←(repr_quot a).property, ←(repr_quot b).property],
    have p₀ := quot_gauche_exact _ _ pab,
    cases p₀ with k t, cases t with k_K p₀,
    apply quot.sound,
    existsi (⟨k, KinH.h _ k_K⟩:H), existsi k_K,
    apply subtype.eq,
    exact p₀,
  end
}

@[instance] lemma HdK_distingue_dans_GdK {G : groupe} (H K : sous_groupe G) [KinH : K ⊆₁ H] [dK : K⊲G] [dH : H⊲G]
  : ((H/*(K↘H)) ↪ (G/*K)) ⊲ (G/*K) := plongeon_HdK_GdK_im_distingue H K



theorem theoreme_isomorphisme₃ {G : groupe} (H K : sous_groupe G) [dH : H⊲G] [dK : K⊲G] [KinH : K ⊆₁ H] 
  : G/*H ≋ (G/*K) /* (H/*(K↘H) ↪ (G/*K)) :=
begin
  -- Preuve du polycopié : 
    -- On définit la composée naturelle f : G → G/K → (G/K)/(H/K)
    -- Elle est surjective comme composée des fonctions de classe qui sont surjectives
    -- On montre que son noyeau est égal à H
    -- On applique le premier théorème d'isomorphisme à f 
  let f := (mor_quotient (H/*(K↘H) ↪ (G/*K))) ∘₁ (mor_quotient K), 
  have f_surj : function.surjective f := function.surjective.comp mor_quotient_surj mor_quotient_surj,
  have ker_f_eq_H : ↩ker f = H,
    rw [sous_groupe_eq_iff, sous_groupe_de_est_sous_groupe_id, ←set_eq],
    intro a, have p₂ : f a = ⟦⟦a⟧@K⟧@((H/*(K↘H) ↪ G/*K)) := rfl,
    rw [←im_one_in_ker,p₂, class_one_iff],
    have p₃ : (H/*(K↘H) ↪ (G/*K)) = ↩im plongeon_HdK_GdK := rfl,
    split;intro pa; rw p₃ at *, {
      cases pa with A pA,
      rw [plongeon_HdK_GdK_id] at pA,
      have pA' := quot_gauche_exact _ _ pA,
      cases pA' with k t, cases t with k_K pk,
      rw pk,
      exact H.mul_stab _ (repr_quot A).val.property _ (KinH.h _ k_K),
    }, {
      existsi ⟦⟨a, pa⟩⟧@(K↘H),
      rw plongeon_HdK_GdK_id₂, 
    },
  have p₀ : G/*↩ker f ≋ (G/*K) /* (H/*(K↘H) ↪ (G/*K)) := theoreme_isomorphisme₁_surj f_surj, 
  simp only [ker_f_eq_H] at p₀,
  exact p₀,
end

end groupe


end