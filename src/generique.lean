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

end generique