


import .generique
open generique


section

universe u
 


/-*******************************Définitions et coercions de base ******************************-/

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
structure groupe : Type (u+1) :=
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
  (sous_ens : set G.ens)
  (mul_stab : ∀ a b ∈ sous_ens, G.mul a b ∈ sous_ens)
  (inv_stab : ∀ a ∈ sous_ens, a⁻¹ ∈ sous_ens)
  (contient_neutre : G.neutre ∈ sous_ens )


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
-- Coertion utile quand on veut voir un sous groupe comme un ensemble (ex: déf de distingué)
instance sous_groupe_to_sous_ens {G: groupe} 
  : has_coe (sous_groupe G) (set G) :=
  ⟨λ H, H.sous_ens⟩ 

-- Définition d'un morphisme de groupes
structure morphisme (G H : groupe) :=
  (mor : G → H)
  (resp_mul : ∀ a b : G, mor (a*b) = (mor a) * (mor b) )

-- Permet de voir un morphisme comme l'application sous-jacente quand c'est nécessaire
instance morphisme_to_fonction {G H : groupe}
  : has_coe_to_fun (morphisme G H) (λ _, G → H) :=
  ⟨λ m, m.mor⟩


section -- exemples d'utilisation transparente des coercions

variables (G G' G'': groupe) (H : sous_groupe G)

-- ici G est vu comme G.ens, G' comme G'.ens et H comme {a : G.ens // a∈H.sous_ens}
variables (g₁ g₂ : G) (g₁' g₂' : G') (h₁ h₂ : H) 

variables (f : morphisme G G') (g : morphisme G' G'') (h : morphisme G' H)

example : G' := f g₁ -- ici f est vu comme f.mor

/-
Dans cet exemple plusieures inférences intérviennent : 
1) Comme f est utilisée comme fonction, f est vue comme f.mor
2) Comme g₁ : G.ens et que G.ens a une instance de has_mul, * est interpété comme G.mul
3) Comme on veut appliquer G.mul à h₁ : {a : G.ens // a∈H.sous_ens}, h₁ est vu comme h₁.val : G.ens
-/
example : G' := f (g₁*h₁) 

-- Ici G est vu comme G.ens, H comme {a : G.ens // a∈H.sous_ens}
-- et on peut définir la composée des deux morphismes simplement : 
example : G → H := h∘f

end -- fin exemples



-- permet d'avoir accès à tous les théorèmes sous le même nom que la structure
-- permet également de "cacher" nos noms de théorèmes pour éviter les conflits 
namespace groupe


lemma neutre_droite (G : groupe) : ∀ a : G.ens, a*1 = a :=
 sorry

lemma inv_droite (G: groupe) : ∀ a : G.ens, a * a⁻¹ = 1 :=
  sorry


lemma neutre_unique {G: groupe} (e : G.ens) (h : ∀ a, e*a = a ) : e = 1 :=
  begin
  have h1 := h 1,
  rw neutre_droite at h1,
  rwa h1,
  end

lemma inv_unique (G: groupe) {a : G} {b : G} (h: b*a = 1) : b = a⁻¹ :=
  sorry

lemma inv_of_mul (G: groupe) (a b : G) : (a*b)⁻¹ = b⁻¹ * a⁻¹ :=
  sorry

lemma inv_involution (G : groupe) (a : G) : (a⁻¹)⁻¹ = a :=
  sorry

lemma mul_droite_div_droite (G : groupe) (a b c : G) : a * b = c ↔ a = c * b⁻¹ :=
  sorry

lemma mul_gauche_div_gauche (G : groupe) (a b c : G) : a * b = c ↔ b = a⁻¹ * c :=
  sorry

lemma mul_assoc' (G : groupe) (a b c : G) : a * b * c = a * (b * c) := G.mul_assoc a b c

def puissance {G: groupe} (x : G) (n : ℤ) : G :=
  begin
    induction n with m m',
      induction m with k hk, -- si c'est m avec m ≥ 0
        exact G.neutre, -- si c'est 0
        exact hk*x, -- si c'est k+1 avec k>=0 et x^k = hk
      induction m' with k hk, -- si c'est -(m' + 1) avec m' ≥ 0
        exact x⁻¹, -- si c'est -1
        exact hk*x⁻¹ -- si c'est -(n+1) avec x^(-n) = hk
  end 

instance {G: groupe} : has_pow G ℤ :=  ⟨puissance⟩

def est_sous_groupe {G: groupe} (A : set G) : Prop 
  := (∀ a ∈ A, a⁻¹ ∈ A) ∧ (∀ a b ∈ A, a*b ∈ A) ∧ (G.neutre ∈ A)


def sous_groupe_engendre {G: groupe} (A : set G) : set G :=
  ⋂ X : {X': set G // est_sous_groupe X' ∧ A ⊆ X'}, X.val

def sous_groupe_engendre₂ {G: groupe} (A : set G) : set G := 
  let F := (λ a:{x//A x}×bool, if a.snd = tt then a.fst.val else a.fst.val⁻¹) in 
  {x | ∃ L : list ({x//A x}×bool), x = prod_all L F}

lemma engendre_est_sous_groupe {G : groupe} (A : set G)
  : est_sous_groupe (sous_groupe_engendre A) :=
begin
  split; unfold sous_groupe_engendre,
  begin -- preuve que ∀ a ∈ sous_groupe_engendre A, a⁻¹ ∈ sous_groupe_engendre A
    intros, unfold Inter at *,
    intro B, exact B.property.left.left a (H B)
  end, split, 
  begin -- preuve que ∀ a b ∈ sous_groupe_engendre A, a*b ∈ sous_groupe_engendre A
    intros, unfold Inter at *,
    intro B, exact B.property.left.right.left a (H B) b (H_1 B)
  end,
  begin -- preuve que 1 ∈ sous_groupe_engendre A
    unfold Inter, intro B, exact B.property.left.right.right
  end
end

lemma engendre_est_sous_groupe₂ {G : groupe} (A : set G)
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
    end, split, 
    begin -- Preuve que la multiplication est stable
      intros, 
      cases H with decomp_a ha, cases H_1 with decomp_b hb, 
      apply Exists.intro (decomp_a ++ decomp_b), 
      rw mul_prod_of_concat decomp_a decomp_b _ G.neutre_gauche G.mul_assoc, 
      rw ←ha, rw ←hb,
    end,
    by {apply Exists.intro [], unfold prod_all, refl} -- G.neutre ∈ sous_groupe_engendre₂ A 
end

def mul_gauche_ens {G : groupe} (a : G) (H : set G) : set G :=
  {g : G | ∃ h ∈ H, g = a*h}
def mul_droite_ens {G : groupe} (H : set G) (a : G) : set G :=
  {g : G | ∃ h ∈ H, g = h*a}

def est_distingue {G : groupe} (H : sous_groupe G) : Prop :=
  ∀ a:G, mul_gauche_ens a H = mul_droite_ens H a

def rel_gauche_mod {G : groupe} (H : sous_groupe G) : G → G → Prop :=
  λ x y : G, y ∈ mul_gauche_ens x H 
def rel_droite_mod {G : groupe} (H : sous_groupe G) : G → G → Prop :=
  λ x y : G, y ∈ mul_droite_ens ↑H x 

@[instance] def rel_equivalence_gauche {G : groupe} (H : sous_groupe G) : setoid G := ⟨
  rel_gauche_mod H,
  begin
    split,
    begin
    intro, apply Exists.intro (1:G), rw G.neutre_droite,
    apply Exists.intro H.contient_neutre, refl
    end,
    split,
    begin
      intros x y hxy, cases hxy with g hg, cases hg with hg eg,
      have ge := eg.symm, 
      rw ← (G.mul_droite_div_droite x g y).symm at ge,
      apply Exists.intro g⁻¹, apply Exists.intro (H.inv_stab g hg),
      exact ge,   
    end,
    begin
      intros x y z hxy hyz, cases hxy with g hg, cases hyz with g₂ hg₂,
      cases hg with hg eg, cases hg₂ with hg₂ eg₂, 
      rw eg at eg₂, rw G.mul_assoc' x g g₂ at eg₂,
      apply Exists.intro (g*g₂), apply Exists.intro (H.mul_stab g hg g₂ hg₂),
      exact eg₂,
    end,
  end
⟩

def ensemble_quotient_gauche {G : groupe} (H : sous_groupe G) : set (set G)
  := classes_equivalence (rel_equivalence_gauche H)

def groupe_quotient {G : groupe} (H : sous_groupe G) (dH : est_distingue H) : groupe :=
let G_H := ensemble_quotient_gauche H in
{
 ens := {A : set G // A ∈ G_H },
 mul := sorry,
 inv := sorry,
 neutre := sorry,
 inv_gauche := sorry,
 mul_assoc := sorry, 
 neutre_gauche := sorry,
}


section

-- Pour définir l'ordre, (∃ n : ℕ, x^(n:ℤ) = 1) n'est pas une proposition décidable en général
-- Il faut donc utiliser le module classical pour que toutes les propositions soient décidables
open classical
local attribute [instance, priority 10] prop_decidable

noncomputable def ordre {G : groupe} (x : G) : ℕ :=
  if h : (∃ n : ℕ, x^(n:ℤ) = 1) then nat.find h else 0


end
/-******************************Fin Définitions et coercions de base *****************************-/







theorem mor_neutre_est_neutre {G H : groupe} {f : morphisme G H} : f 1 = 1 :=
  sorry

theorem mor_inv_inv_mor {G H : groupe} {f : morphisme G H}  (a : G) : f a⁻¹ =  (f a)⁻¹ :=
  sorry


def ker {G H : groupe} (f : morphisme G H) : set G :=
  {a : G.ens | f a = 1}

def im {G H : groupe} (f : morphisme G H) : set H :=
  {b : H | ∃ a : G, f a = b }

def ens_reciproque {G H : groupe} (f : morphisme G H) (B: set H) :=
  {a : G | f a ∈ B }

def ens_image {G H : groupe} (f : morphisme G H) (A: set G) :=
  {b : H | ∃ a ∈ A, f a = b}

def comp {G H K: groupe} (f : morphisme G H) (g : morphisme H K) : morphisme G K := 
  sorry


theorem ker_comp_eq_inv_ker {G H K: groupe} (f : morphisme G H) (g : morphisme H K) 
  : ker (comp f g) = ens_reciproque f (ker g) :=
  sorry

theorem im_comp_eq_im_im {G H K: groupe} (f : morphisme G H) (g : morphisme H K) 
  : im (comp f g) = ens_image g (im f) :=
  sorry 


def isomorphisme {G H: groupe } (f : morphisme G H) :=
  ∃ g : morphisme H G, (∀ a : G,  g (f a) = a)



end groupe


end