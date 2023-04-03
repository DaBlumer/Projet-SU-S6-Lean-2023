/-
Fichier pour les définitions génériques qui ne sont pas liées aux groupes mais peuvent être utiles
-/
namespace generique

def Union {α : Type*} {I : Type*} (F : I → set α) : set α :=
  {x | ∃ i, x ∈ F i}

def Inter {α : Type*} {I : Type*} (F : I → set α) : set α :=
  {x | ∀ i, x ∈ F i}

notation `⋃` binders `,` expr_i:(scoped f, Union f) := expr_i
notation `⋂` binders `,` expr_i:(scoped f, Inter f) := expr_i

instance {α : Type*} : has_subset (set α) :=
  ⟨λ A B, ∀ a ∈ A, a ∈ B ⟩
instance {α : Type*} : has_union (set α) :=
  ⟨λ A B, {x | x ∈ A ∨ x ∈ B}⟩
instance {α : Type*} : has_inter (set α) :=
  ⟨λ A B, {x | x ∈ A ∧ x ∈ B}⟩

def prod_all {α : Type*} {β : Type*} [has_mul β] [has_one β] : (list α) → (α → β) →  β
  | [] _ := (1 : β)
  | (a :: l) F := (F a) * prod_all l F

lemma mul_prod_of_concat {α: Type*} {β : Type*} [has_mul β] [has_one β] 
  (l₁ l₂ : list α) (f : α → β) (h: ∀ x:β, (1:β)*x = x) (mul_assoc : ∀ x y z : β, x*y*z = x*(y*z))
  : prod_all (l₁++l₂) f = (prod_all l₁ f) * (prod_all l₂ f) :=
begin
  induction l₁, 
  have h' : list.nil ++ l₂ = l₂, refl, rw h', unfold prod_all, rw h _, -- si l₁ = []
  rw list.cons_append, unfold prod_all, rw l₁_ih, rw mul_assoc, 
end

class {u v} has_quotient_gauche (A : out_param (Type u)) (B : Type v) :=
  (quotient : B → Type max u v)
class {u v} has_quotient_droite (A : out_param (Type u)) (B : Type v) :=
  (quotient : B → Type max u v)

notation G ` /. `:35 H:34 := has_quotient_gauche.quotient H
notation H ` .\ `:35 H:34 := has_quotient_droite.quotient H

def nat_pow (n : ℕ) : ℕ → ℕ
  | 0 := 1
  | (nat.succ k) := n*(nat_pow k)

instance nat_has_pow : has_pow ℕ ℕ := ⟨nat_pow⟩



theorem push_exists_prop {α : Type*} {p : α → Prop} (h : ∃ a, p a) 
  : ∃ a : {a' // p a'}, true :=
  begin
    cases h with a ha, 
    apply Exists.intro,
    exact ⟨a, ha⟩,
    apply true.intro,  
  end

noncomputable def choose {α : Type*} {p : α → Prop} (h : ∃ a, p a) : {a // p a} :=
  (classical.inhabited_of_exists (push_exists_prop h)).default

theorem prop_of_choose {α : Type*} {p : α → Prop} (h : ∃ a, p a)
  : p (choose h).val := (choose h).property 

section
universe u_1
open classical
local attribute [instance, priority 10] prop_decidable

theorem simp_dite : ∀ {α : Type u_1} {p : Prop} [decidable p] {f : p → α} {g : ¬p → α} (h : p), dite p f g = f h :=
λ {α : Type u_1} {p : Prop} [_inst_1 : decidable p] {f : p → α} {g : ¬p → α} (h : p),
  (id_tag tactic.id_tag.simp
     ((λ (a a_1 : α) (e_1 : a = a_1) (ᾰ ᾰ_1 : α) (e_2 : ᾰ = ᾰ_1), congr (congr_arg eq e_1) e_2) (dite p f g)
        (f h)
        (dif_pos h)
        (f h)
        (f h)
        (eq.refl (f h)))).mpr
    (eq.refl (f h))

theorem simp_dite_neg : ∀ {α : Type u_1} {p : Prop} [_inst_1 : decidable p] {f : p → α} {g : ¬p → α} (h : ¬p), dite p f g = g h :=
λ {α : Type u_1} {p : Prop} [_inst_1 : decidable p] {f : p → α} {g : ¬p → α} (h : ¬p),
  (id_tag tactic.id_tag.simp
     ((λ (a a_1 : α) (e_1 : a = a_1) (ᾰ ᾰ_1 : α) (e_2 : ᾰ = ᾰ_1), congr (congr_arg eq e_1) e_2) (dite p f g)
        (g h)
        (dif_neg h)
        (g h)
        (g h)
        (eq.refl (g h)))).mpr
    (eq.refl (g h))

lemma int_mod_add_div
  : ∀ (a : ℤ) (b : ℕ) , a = (a/b)*b + a%b
| (m : ℕ) (n : ℕ) :=
  begin
    unfold has_div.div, unfold int.div, unfold has_mod.mod, unfold int.mod,
    have why : ∀ z : ℕ, (z:ℤ).nat_abs = z, intro, refl,
    rw [why, ← int.coe_nat_eq, ←int.coe_nat_mul, ← int.coe_nat_add, int.coe_nat_eq_coe_nat_iff],
    apply eq.symm, rw [nat.mul_comm, nat.add_comm],
    exact nat.mod_add_div m n,
  end
| -[1+ m] 0       :=
  begin
    unfold has_div.div, rw int.coe_nat_zero, unfold int.div,
    unfold has_mod.mod, unfold int.mod,
    rw [int.mul_zero, int.zero_add, ← int.coe_nat_zero],
    have why : ∀ z : ℕ, (z:ℤ).nat_abs = z, intro, refl,
    rw why, rw nat.mod_zero, refl,
  end
| -[1+ m] (n+1:ℕ) :=
  begin
    unfold has_div.div, unfold int.div,
    unfold has_mod.mod, unfold int.mod,
    have why : ∀ z : ℕ, (z:ℤ).nat_abs = z, intro, refl, rw why,
    have why₂ : ∀ z : ℕ, -[1+ z] = -z.succ, intro, refl, 
    rw [why₂ (m/n.succ), int.neg_eq_neg_one_mul, int.mul_assoc, ← int.coe_nat_mul],
    rw [nat.succ_mul],
    have h₁ := nat.mod_add_div m n.succ, rw nat.add_comm at h₁,
    have h₂ : n.succ * (m / n.succ) + m % n.succ - m % n.succ = m - m % n.succ := by {rw h₁},
    rw [nat.add_sub_cancel, nat.mul_comm] at h₂,
    rw h₂,
    have h₃ : (m % (n + 1)).succ - (n + 1) = 0,
      rw nat.succ_sub_succ,
      unfold has_sub.sub, cases n,
        unfold nat.sub, rw nat.zero_add, rw nat.mod_one,
        have h' : n.succ + 1 > 0, exact nat.zero_lt_succ _,
        have h₃ := nat.mod_lt m h',
        have h₄ := nat.le_of_lt_succ h₃,
        have h₅ := nat.sub_le_sub_right h₄ n.succ,
        rw nat.sub_self at h₅,
        exact nat.eq_zero_of_le_zero h₅,
    rw int.sub_nat_nat_of_sub_eq_zero h₃,
    rw [← int.coe_nat_eq, int.coe_nat_add, int.coe_nat_add],
    rw [int.distrib_left, ← int.neg_eq_neg_one_mul, ← int.neg_eq_neg_one_mul],
    rw [int.coe_nat_sub (nat.mod_le m n.succ)],
    have h₄ := nat.succ_le_succ (nat.le_of_lt_succ (nat.mod_lt m (nat.zero_lt_succ n))),
    rw int.coe_nat_sub h₄,
    rw [int.neg_eq_neg_one_mul, int.neg_eq_neg_one_mul (↑n + ↑1), int.distrib_left],
    repeat{rw [int.coe_nat_succ]},
    repeat {rw int.sub_eq_add_neg},
    rw [int.distrib_left], repeat {rw ← int.neg_eq_neg_one_mul},
    have negneg : ∀ z : ℤ, -(-z) = z, intro,
      rw [int.neg_eq_neg_one_mul, int.neg_eq_neg_one_mul z, ← int.mul_assoc],
      have : (-1:ℤ)*(-1) = 1, refl,
      rw this, rw int.one_mul,
    rw negneg,
    rw [int.coe_nat_zero, int.zero_add],
    rw [int.add_assoc, int.add_comm (-↑n) (-1), int.add_assoc (-1) (-↑n)],
    rw [← int.add_assoc (-↑n), ← int.add_assoc (-↑n), int.add_left_neg (↑n)],
    rw [int.zero_add, ← int.add_assoc (-1), int.add_left_neg 1, int.zero_add],
    rw [int.neg_eq_neg_one_mul (↑(m % n.succ) + 1), int.distrib_left],
    rw [ ← int.neg_eq_neg_one_mul, ← int.neg_eq_neg_one_mul ],
    rw [int.add_assoc, ← int.add_assoc ↑(m % n.succ), int.add_right_neg, int.zero_add],
    have hf : -[1+ m] = -m.succ, refl, rw hf,
    rw int.coe_nat_succ,
    conv {to_lhs, rw int.neg_eq_neg_one_mul, rw int.distrib_left},
    rw ← int.neg_eq_neg_one_mul, rw ← int.neg_eq_neg_one_mul,
  end

lemma int_mod_domaine
  : ∀ (a : ℤ) (b : ℕ) , b > 0 → a%b < b ∧ a%b ≥ 0
| (m : ℕ) (n : ℕ) :=
  begin
    unfold has_mod.mod, unfold int.mod,
    have why : ∀ z : ℕ, (z:ℤ).nat_abs = z, intro, refl,
    intro h,
    split,
    rw [why n, int.coe_nat_lt_coe_nat_iff],
    exact nat.mod_lt _ h,
    rw [← int.coe_nat_zero], apply int.coe_nat_le_coe_nat_of_le,
    exact nat.zero_le _,
  end
| -[1+ m] 0       :=
  begin
    intro h, exfalso, exact nat.not_lt_zero 0 h,
  end
| -[1+ m] (n+1:ℕ) :=
  begin
    intro h,
    unfold has_mod.mod, unfold int.mod,
    have why : ∀ z : ℕ, (z:ℤ).nat_abs = z, intro, refl, rw why,
    have h₁ : (n+1) ≥ (m%(n+1)).succ,
      exact nat.succ_le_succ (nat.le_of_lt_succ (nat.mod_lt m (nat.zero_lt_succ n))),
    rw int.sub_nat_nat_of_le h₁,
    rw [← int.coe_nat_eq, int.coe_nat_sub h₁, int.sub_eq_add_neg],
    split,
    { -- a%b < b
      have h₂ : (-↑((m % (n + 1)).succ) : ℤ) < 0,
        rw ← int.add_left_neg (↑((m % (n + 1)).succ)),
        conv {to_lhs, rw ← int.add_zero (-↑((m % (n + 1)).succ))},
        apply int.add_lt_add_of_le_of_lt,
          exact int.le_refl _,
          rw [← int.coe_nat_zero, int.coe_nat_lt_coe_nat_iff], exact nat.zero_lt_succ _,
      conv {to_rhs, rw ← int.add_zero ↑(n+1)},
      apply int.add_lt_add_of_le_of_lt,
        refl,
        exact h₂,
    },
    { -- a%b ≥ 0
      --rw ← int.sub_eq_add_neg,
      rw ← int.add_right_neg ↑((m % (n + 1)).succ),
      apply int.add_le_add,
        rw int.coe_nat_le_coe_nat_iff, exact h₁,
        refl,
    }

  end


end

end generique