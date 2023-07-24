


import .generique
import .cardinalite_finie
open generique


section

 


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
class groupe : Type 1 :=
  (ens : Type)
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
instance groupe_to_ens : has_coe_to_sort groupe (Type) :=
  ⟨λ a : groupe, a.ens⟩

@[reducible]
instance groupe_has_mul (G : groupe) :
  has_mul (G.ens) := ⟨G.mul⟩

instance groupe_has_one (G: groupe) :
  has_one (G.ens) := ⟨G.neutre⟩

instance groupe_has_inv (G: groupe) :
  has_inv (G.ens) := ⟨G.inv⟩


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
notation G `→*`:51 H:51 := morphisme G H

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
notation g `∘₁`:51 f := comp_mor g f


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


end groupe

end