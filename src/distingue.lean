import .generique
import .cardinalite_finie
import base
import sous_groupes
open generique


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

namespace groupe
/-
Définitions de gH et Hg et notations pour ces deux multiplications 
-/
def mul_gauche_ens {G : groupe} (a : G) (H : set G) : set G :=
  {g : G | ∃ h ∈ H, g = a*h}
def mul_droite_ens {G : groupe} (H : set G) (a : G) : set G :=
  {g : G | ∃ h ∈ H, g = h*a}

notation a ` *₂ `:51 H:51 :=  mul_gauche_ens a H
notation H ` *₃ `:51 a:51 := mul_droite_ens H a



/-
- Classe représentant une preuve qu'un sous groupe est distingué 
- On choisit comme définition H ⊲ G ↔ ∀ g : G, gH = Hg   
- C'est une classe pour permettre à lean de déduire une telle instance du contexte pour certains théorèmes (par
  exemple, dans le thèorème d'isomorphisme 1, pas besoin de dire explicitement que ker f est distingué, lean le saura seul)
-/
class est_distingue {G : groupe} (H : sous_groupe G) : Prop :=
  (h : ∀ a:G, a *₂ H = H *₃ a)
-- ↓ Notation canonique pour un sous groupe qui est distingué. ⊲ s'écrit \vartr  
notation H `⊲`:51 G := @est_distingue G H


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

end groupe
