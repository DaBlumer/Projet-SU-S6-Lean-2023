
import .generique
import .cardinalite_finie
import base
import sous_groupes

open generique

namespace groupe

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






/-*********************************Définitions et lemmes ordre et groupe cyclique **************************************-/

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


/-*******************************FIN Définitions et lemmes ordre et groupe cyclique ************************************-/

end groupe

