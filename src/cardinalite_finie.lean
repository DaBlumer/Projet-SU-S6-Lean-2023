/-
Fichier définissant la cardinalité des types finis 
-/

import .generique
open generique

section
universes u v
structure bijections (E: Type u) (F : Type v) :=
  (f : E → F)
  (f_inv : F → E)
  (inv_gauche : function.left_inverse f_inv f)
  (inv_droite : function.right_inverse f_inv f)

def bijections' (E : Type u) (F : Type v) :=
  {f : E → F // function.bijective f}

end

def bijection'_of_bijection {E : Type*} {F : Type*} (bij : bijections E F) 
  : bijections' E F := ⟨bij.f, 
  begin 
    split, 
      {
        intros a b h,
        have h₂: bij.f_inv (bij.f a) = bij.f_inv (bij.f b), rw h, 
        repeat {rw bij.inv_gauche at h₂},
        exact h₂
      },
      {
        intro b,
        apply Exists.intro (bij.f_inv b),
        exact bij.inv_droite _, 
      },
  end⟩ 



noncomputable def bijection_of_bijection' {E: Type*} {F: Type*} (bij' : bijections' E F) 
  : bijections E F := 
  {
    f := bij'.val,
    f_inv := λ e, (choose (bij'.property.2 e)).val,
    inv_gauche :=
      begin
        intro,
        simp, 
        have h₁ := prop_of_choose (bij'.property.2 (bij'.val x)),
        apply bij'.property.1, 
        exact h₁,
      end,
    inv_droite := 
      begin
        intro,
        simp, 
        exact prop_of_choose (bij'.property.2 x), 
      end, 
  }   

def permutations (E : Type*) := bijections' E E 

-- Un ensemble E est fini si il existe une injection de E dans ⟦0, n-1⟧ pour un certain n
class est_fini (E : Type*) := 
  (majorant : ℕ)
  (f : E → fin majorant)
  (f_inj : function.injective f)


class cardinal' (E : Type*) :=
  (card : ℕ)
  (bij : bijections E (fin card))

def cardinal_est (E : Type*) (n : ℕ) : Prop :=
  nonempty (bijections E (fin n)) 


section -- On a besoin du principe du tiers exclu pour montrer ça
open classical
local attribute [instance, priority 10] prop_decidable


noncomputable def fini_a_cardinal_fini (E : Type*) [h : est_fini E] : cardinal' E :=
begin
  unfreezingI { cases h with n f hf },
  induction n with m hm, 
    {
      apply cardinal'.mk 0,
      --cases hn with f hf, 
      let inv_f : fin 0 → E := λ n,
        by  {apply false.elim, exact nat.not_lt_zero n.val n.property},
      apply bijections.mk f inv_f; intro; apply false.elim,
        {exact nat.not_lt_zero (f x).val (f x).property},
        {exact nat.not_lt_zero (f (inv_f x)).val (f (inv_f x)).property }
    },
    {
      --cases hn with f hf,
      exact (
        if h : nonempty {k : fin m.succ // ∀ e, f e ≠ k} then
        begin
          --apply hm, 
          cases (@arbitrary {k // ∀ e, f e ≠ k} (inhabited_of_nonempty h)) with k hk, 
          cases k with kv kp,
          exact (
            if h2 : (kv = m) then
            begin
              let f' : E → fin m := λ e, ⟨(f e).val, begin
                have hke := hk e, simp at hke,  
                cases (f e) with fe hfe, simp,
                have h3 := nat.le_of_succ_le_succ hfe,
                cases (nat.eq_or_lt_of_le h3) with il ir,
                  exfalso, exact hke (by {apply fin.eq_of_veq, simp [h2, il]}),
                  assumption, 
              end⟩, 
              apply hm f', intros a b hab, 
              have hab' := fin.eq_of_veq (fin.mk.inj hab),
              exact hf hab',  
            end
            else 
            begin
              let f' : E → fin m := λ e,
                if hfe : (f e).val = m then
                  ⟨kv, begin
                    cases (nat.eq_or_lt_of_le (nat.le_of_succ_le_succ kp)) with il ir, 
                      contradiction,
                      assumption,
                  end⟩
                else
                  ⟨(f e).val, nat.lt_of_le_and_ne (nat.le_of_lt_succ(f e).property) hfe⟩,
              apply hm f', intros a b hab, 
              cases eq.decidable (f a).val m with df dt,
              {
                have a' : (f' a).val = (f a).val, simp [df, f'],
                have df' : (f b).val ≠ m, intro hf,
                  have b' : (f' b).val = kv, simp [f', hf], 
                  rw← hab at b', rw a' at b', rw b' at df,
                  have hka := hk a, 
                  have : (f a) = ⟨kv, kp⟩, apply fin.eq_of_veq, simp, exact b', 
                  contradiction, 
                have b' : (f' b).val = (f b).val, simp [df', f'], 
                have gg : (f' a).val = (f' b).val, apply fin.veq_of_eq, assumption,
                have gg' : (f a).val = (f b).val, simp [gg, ←a', ←b'], 
                have : (f a)=(f b), apply fin.eq_of_veq, assumption,
                exact hf this
              },
              {
                have a' : (f' a).val = kv, simp [dt, f'],
                cases eq.decidable (f b).val m with df' dt', 
                  {
                    exfalso,
                    have b' : (f' b).val = (f b).val, simp[df', f'], 
                    have fv : (f' a).val = (f' b).val, exact fin.veq_of_eq hab,
                    rw b' at fv, rw a' at fv,
                    have fv' := eq.symm fv, 
                    have hkb := hk b,
                    have : (f b = ⟨kv, kp⟩), apply fin.eq_of_veq, simp, assumption,
                    contradiction, 
                  }, 
                  {
                    have fab : (f a).val = (f b).val, rw dt, rw dt', 
                    have : f a = f b, apply fin.eq_of_veq, assumption,
                    exact hf this, 
                  }
              }
            end
          ),
        end
        else 
        begin
          apply cardinal'.mk m.succ,
          have surjf : ∀ k, inhabited  {e// f e = k},
            intro k, 
            cases prop_decidable (nonempty {e // (f e) = k}) with exi nexi,
            {
              exfalso,
              have : ∀ e', f e' ≠ k, intro e', intro fek, exact exi ⟨⟨e', fek⟩⟩, 
              exact h ⟨⟨k, this⟩⟩,  
            },
            exact classical.inhabited_of_nonempty nexi, -- CLASSICAL  
          let f_inv : fin m.succ → E := λ ki, 
            (@arbitrary {e // f e = ki} (surjf ki)),
          apply bijections.mk f f_inv, 
          {
            intro x, 
            simp [f_inv],
            apply hf, apply (@arbitrary {e // f e = f x} (surjf (f x))).property, 
          },
          {
            intro y, 
            simp [f_inv],
            apply  (@arbitrary {e // f e = y} (surjf y)).property,
          }, 
        end
      ),
    }
end

noncomputable def cardinal (E : Type*) [h : est_fini E] : ℕ := (fini_a_cardinal_fini E).card

universes u v
instance set_to_type {E : Type u} : has_coe (set E) (Type u) := ⟨λ S, {x//S x}⟩

variables (E : Type u) (F : Type v) {n m : ℕ} [h : est_fini E] [h' : est_fini F] (E' E'' : set E)


protected def my_func (e : E×F): fin (h.majorant*h'.majorant + 1) :=
fin.mk (h'.majorant * (h.f e.1).val + (h'.f e.2).val)
      (begin
        cases nat.decidable_lt 0 h'.majorant with ff tt,
        {
          have h₁ : h'.majorant = 0, 
            cases nat.eq_or_lt_of_not_lt ff with a b,
              apply eq.symm, exact a,
              exfalso, exact nat.not_lt_zero h'.majorant b,
          simp only [h₁, nat.mul_zero, nat.zero_mul, nat.zero_add],
          have h₂ := (h'.f e.2).property, simp only [h₁] at h₂,
          have h₃ : 0 < 1, exact nat.zero_lt_succ 0,
          exact nat.lt_trans h₂ h₃,  
        },
        {
          have h₁ := (h.f e.1).property,
          cases nat.decidable_lt 0 h.majorant with f t,
          {
            exfalso,
            have h₂ : h.majorant = 0, 
              cases nat.eq_or_lt_of_not_lt f with a b,
                apply eq.symm, exact a,
                exfalso, exact nat.not_lt_zero h.majorant b,
            simp only [h₂] at h₁,
            exact nat.not_lt_zero (h.f e.1).val h₁,  
          },
          {
            have h₂ : ∀ n m : ℕ, n < m → n ≤ m.pred,
              intros n m hnm, cases m,
                exfalso, exact nat.not_lt_zero _ hnm,
                rw nat.pred_succ, exact nat.le_of_lt_succ hnm, 
            have h₃ : (h.f e.1).val ≤ h.majorant.pred, exact h₂ _ _ (h.f e.1).property, 
            have h₄ : h'.majorant*(h.f e.1).val ≤ h'.majorant*h.majorant.pred := nat.mul_le_mul_of_nonneg_left h₃,
            have h₅ := nat.add_le_add_right h₄ (h'.f e.2).val,
            have h₆ := nat.add_lt_add_left (h'.f e.2).property (h'.majorant*h.majorant.pred),
            have h₇ := nat.lt_of_le_of_lt h₅ h₆, 
            have h₈ : h.majorant.pred.succ = h.majorant, exact nat.succ_pred_eq_of_pos t,
            simp only [← h₈] {single_pass := tt},
            simp only [nat.succ_mul], 
            apply nat.lt_succ_of_lt,
            rw nat.mul_comm _ h'.majorant,
            exact h₇,
          }
        }
      end)

lemma my_func_ident (e : E×F) : (@my_func E F h h' e).val = (h'.majorant * (h.f e.1).val + (h'.f e.2).val)
  := begin
    simp only [my_func], 
  end

@[instance]
def prod_card_fini : est_fini (E×F) :=
  {
    majorant := h.majorant*h'.majorant+1,
    f := @my_func E F h h', 
    f_inj :=
      begin
        intros a b hab,
        simp only [my_func] at hab, 
        have h₁ := fin.veq_of_eq hab, 
        simp at h₁, 
        have h₂ := (h'.f a.2).property,
        have h₃ := (h'.f b.2).property,
        have h₄ := h'.majorant * ((h.f a.1).val - (h.f b.1).val) = (h'.f b.2).val - (h'.f a.2).val,
        have div_eucl_uniq : ∀ n q₁ q₂ r₁ r₂ : ℕ, n*q₁ + r₁ = n*q₂ + r₂ → r₁ < n → r₂ < n → r₁ = r₂, 
          intro n, intro q₁, revert n, 
          induction q₁ with k hk; intros n q₂ r₁ r₂ hh₁ hh₂ hh₃, 
            {rw [nat.mul_zero, nat.zero_add] at hh₁, rw hh₁ at hh₂,
            cases q₂ with q₂,
              rw [nat.mul_zero, nat.zero_add] at *, exact hh₁,
              rw [nat.mul_succ, nat.add_comm _ n, nat.add_assoc, ← nat.add_zero n, nat.add_assoc] at hh₂,
              have h₅ := nat.lt_of_add_lt_add_left hh₂, 
              exfalso, exact nat.not_lt_zero _ h₅, 
            },
            {
              rw nat.mul_succ at hh₁, 
              cases q₂ with q₂,
                {rw [nat.mul_zero, nat.zero_add] at *, rw← hh₁ at hh₃, 
                exfalso, rw [nat.add_comm _ n, nat.add_assoc, ← nat.add_zero n, nat.add_assoc] at hh₃, 
                have h₅ := nat.lt_of_add_lt_add_left hh₃,
                exact nat.not_lt_zero _ h₅},
                rw [nat.mul_succ, nat.add_comm (n*k) n, nat.add_assoc] at hh₁,
                rw [nat.add_comm _ n, nat.add_assoc] at hh₁,
                have h₆ := nat.add_left_cancel hh₁,
                exact hk n q₂ r₁ r₂ h₆ hh₂ hh₃, 
            },
        have h₅ : (h'.f a.2) = (h'.f b.2) := fin.eq_of_veq (div_eucl_uniq _ _ _ _ _ h₁ h₂ h₃),
        rw h₅ at h₁, 
        have h₆ := nat.add_right_cancel h₁, 
        cases (nat.decidable_lt 0 h'.majorant) with ff tt, 
        {
          have h₇ : h'.majorant = 0,
            cases nat.eq_or_lt_of_not_lt ff with a b,
            apply eq.symm, assumption,
            exfalso, exact nat.not_lt_zero _ b,
          exfalso,
          simp only [h₇] at h₂,
          exact nat.not_lt_zero _ h₂,  
        },
        {
          have h₇ : (h'.majorant * (h.f a.1).val)/h'.majorant = (h.f a.1).val := nat.mul_div_cancel_left _ tt,
          have h₈ := h₇,
          rw h₆ at h₈, 
          have h₉ := nat.mul_div_cancel_left (h.f b.1).val tt,
          rw h₈ at h₉,
          have h₁₀ := fin.eq_of_veq h₉, 
          have H₁ := h'.f_inj h₅,
          have H₂ := h.f_inj h₁₀,
          cases a, cases b, simp at H₁ H₂,
          rw [H₁, H₂],
        }
      end
  }

@[instance]
def func_card_fini : est_fini (E → F) :=
  {
    majorant := h'.majorant ^ h.majorant,
    f := sorry,
    f_inj := sorry 
  }

theorem prod_of_cards [h : est_fini E] [h' : est_fini F]
  : cardinal (E×F) = (cardinal E) * (cardinal F) :=
  sorry

theorem card_of_func [h : est_fini E] [h' : est_fini F]
  : cardinal (E→F) = cardinal F ^ cardinal E :=
  sorry

theorem eq_card_of_idempotents [h : est_fini E] [h' : est_fini F] (bij : bijections E F) 
  : cardinal E = cardinal F := 
  sorry

end -- section utilisant classical