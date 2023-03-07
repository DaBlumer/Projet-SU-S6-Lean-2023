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
end


-- Un ensemble E est fini si il existe une injection de E dans ⟦0, n-1⟧ pour un certain n
def est_fini (E : Type*) : Prop := 
  ∃ n : ℕ, ∃ f : E → fin n, function.injective f

theorem fini_ssi_surjectable (E : Type*)
  : est_fini E ↔ ∃ n : ℕ, ∃ g : fin n → E, function.surjective g :=
  sorry

def cardinal_est (E : Type*) (n : ℕ) : Prop :=
  nonempty (bijections E (fin n)) 


section -- On a besoin du principe du tiers exclu pour montrer ça
open classical
local attribute [instance, priority 10] prop_decidable
theorem fini_a_cardinal_fini {E : Type*} (h : est_fini E) : ∃ n, cardinal_est E n :=
begin
  cases h with n hn,
  induction n with m hm, 
    {
      apply Exists.intro 0,
      cases hn with f hf, 
      apply nonempty.intro,
      let inv_f : fin 0 → E := λ n,
        by  {apply false.elim, exact nat.not_lt_zero n.val n.property},
      apply bijections.mk f inv_f; intro; apply false.elim,
        {exact nat.not_lt_zero (f x).val (f x).property},
        {exact nat.not_lt_zero (f (inv_f x)).val (f (inv_f x)).property }
    },
    {
      cases hn with f hf,
      exact (
        if h : (∃ k : fin m.succ, ∀ e, f e ≠ k) then
        begin
          apply hm, 
          cases h with k hk, 
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
              apply Exists.intro f', intros a b hab, 
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
              apply Exists.intro f', intros a b hab, 
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
          apply Exists.intro m.succ, unfold cardinal_est, apply nonempty.intro, 
          have surjf : ∀ k, inhabited  {e// f e = k},
            intro k, 
            cases prop_decidable (nonempty {e // (f e) = k}) with exi nexi,
            {
              exfalso,
              have : ∀ e', f e' ≠ k, intro e', intro fek, exact exi ⟨⟨e', fek⟩⟩, 
              exact h ⟨k, this⟩,  
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


universe u
instance set_to_type {E : Type u} : has_coe (set E) (Type u) := ⟨λ S, {x//S x}⟩

variables (E F : Type u) {n m : ℕ} {h : cardinal_est E n} {h' : cardinal_est F m} (E' E'' : set E)

theorem prod_of_cards 
  : cardinal_est (E×F) (n*m) :=
  sorry

theorem card_of_func 
  : cardinal_est (E → F) (m^n) :=
  sorry


end -- section utilisant classical