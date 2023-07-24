

import .generique
import .cardinalite_finie
import base 
import sous_groupes
import distingue
open generique



namespace groupe 
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
notation G `≋`:40 G' := sont_isomorphes G G'

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

notation f`↓`:51 := mor_vu_dans_im f

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


def plongeon {G : groupe} (H : sous_groupe G) : H  →* G := ⟨λ h, h.val, coe_mul_sous_groupe⟩
lemma plongeon_id {G : groupe} (H : sous_groupe G) (a : H) : plongeon H a = (a : G):= rfl

end groupe