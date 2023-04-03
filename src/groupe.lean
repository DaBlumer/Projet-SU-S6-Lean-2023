


import .generique
import .cardinalite_finie
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
-- Coertion utile quand on veut voir un sous groupe comme un ensemble (ex: déf de distingué)
instance sous_groupe_to_sous_ens {G: groupe} 
  : has_coe (sous_groupe G) (set G) :=
  ⟨λ H, H.sous_ens⟩ 
instance appartient_sous_groupe {G: groupe} 
  : has_mem G (sous_groupe G) :=
  ⟨λ x H, H.sous_ens x⟩ 

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

lemma mul_assoc' (G : groupe) (a b c : G) : a * b * c = a * (b * c) := G.mul_assoc a b c
lemma inv_gauche' (G : groupe) (a : G) : a⁻¹*a = 1 := G.inv_gauche a
lemma neutre_gauche' (G : groupe) (a : G) : 1*a = a := G.neutre_gauche a



lemma inv_droite (G: groupe) : ∀ a : G.ens, a * a⁻¹ = 1 :=
  sorry

lemma inv_droite' (G : groupe) (a : G) : a*a⁻¹ = 1 := G.inv_droite a

lemma neutre_droite (G : groupe) : ∀ a : G.ens, a*1 = a :=
 begin
 intro a,
 rw ← inv_gauche' G a, 
 rw ← mul_assoc',
 rw inv_droite',
 rw neutre_gauche',
 end

lemma neutre_droite' (G : groupe) (a : G) : a*1 = a := G.neutre_droite a




lemma neutre_unique {G: groupe} (e : G.ens) (h : ∀ a, e*a = a ) : e = 1 :=
  begin
  have h1 := h 1,
  rw neutre_droite at h1,
  rwa h1,
  end









lemma inv_unique (G: groupe) {a : G} {b : G} (h: b*a = 1) : b = a⁻¹ :=
  begin
  rw ← neutre_droite' G b,
  rw ← inv_droite' G a,
  rw ← mul_assoc',
  rw h,
  rw neutre_gauche',
  end

lemma inv_involution (G : groupe) (a : G) : (a⁻¹)⁻¹ = a :=
  begin
  rw ← neutre_droite' G a⁻¹⁻¹,
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
  rw inv_droite' G b,
  rw neutre_droite',
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
  rw inv_droite',
  rw neutre_gauche',
  end

lemma inv_of_mul (G: groupe) (a b : G) : (a*b)⁻¹ = b⁻¹ * a⁻¹ :=
  begin
  rw ← mul_gauche_div_gauche,
  rw ← neutre_droite' G a⁻¹,
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
  rw  [mul_assoc', inv_droite', neutre_droite'] at h, 
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



def puissance_n {G : groupe} (x : G) : ℕ → G
  | nat.zero := 1
  | (nat.succ n) :=  x*(puissance_n n)

instance {G : groupe} : has_pow G ℕ := ⟨puissance_n⟩    

def puissance_z {G : groupe} (x : G) : ℤ → G
  | (int.of_nat n) := x^n
  | (int.neg_succ_of_nat n) := (x^(n+1))⁻¹

instance {G : groupe} : has_pow G ℤ := ⟨puissance_z⟩

lemma coe_pow_nat {G : groupe} {n : ℕ} (x : G) : x ^ n = x ^ (n:ℤ) :=
  begin
    rw int.coe_nat_eq, 
    unfold pow,
    unfold puissance_z,
    unfold pow, 
  end


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

def est_sous_groupe {G: groupe} (A : set G) : Prop 
  := (∀ a ∈ A, a⁻¹ ∈ A) ∧ (∀ a b ∈ A, a*b ∈ A) ∧ ((1:G) ∈ A)


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
    by {apply Exists.intro [], unfold prod_all} -- G.neutre ∈ sous_groupe_engendre₂ A 
end


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
      exact i.property.1.2.2,  
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
        exact i.property.1.2.1 _ h₂ _ h₀, 
      }, 
      {
        simp at hL, 
        have h₀ : prod_all L (λ (a : {x // A x} × bool), ite (a.snd = tt) a.fst.val (a.fst.val)⁻¹) ∈ i.val, 
          have := hR (prod_all L (λ (a : {x // A x} × bool), ite (a.snd = tt) a.fst.val (a.fst.val)⁻¹)),
          apply this, refl,
        have h₁ : e.fst.val ∈ i.val := (i.property.2) e.fst e.fst.property,
        rw hL,
        exact i.property.1.2.1 _ h₁ _ h₀,
      }
    }
  }
end

def mul_gauche_ens {G : groupe} (a : G) (H : set G) : set G :=
  {g : G | ∃ h ∈ H, g = a*h}
def mul_droite_ens {G : groupe} (H : set G) (a : G) : set G :=
  {g : G | ∃ h ∈ H, g = h*a}

def est_distingue {G : groupe} (H : sous_groupe G) : Prop :=
  ∀ a:G, mul_gauche_ens a H = mul_droite_ens H a


lemma carac_est_distingue {G : groupe} (H' : sous_groupe G)
  : est_distingue H' ↔ ∀ h ∈ H', ∀ g : G, g*h*g⁻¹ ∈ H'  :=
  sorry

lemma distingue_droite_to_gauche {G : groupe } {H' : sous_groupe G}
  (dH : est_distingue H') (h ∈ H') (g : G) : ∃ h' ∈ H', g*h = h'*g :=
  sorry

def rel_gauche_mod {G : groupe} (H : sous_groupe G) : G → G → Prop :=
  λ x y : G, y ∈ mul_gauche_ens x H 
def rel_droite_mod {G : groupe} (H : sous_groupe G) : G → G → Prop :=
  λ x y : G, y ∈ mul_droite_ens ↑H x 

local notation G ` %. `:35 H:34 := rel_gauche_mod H
local notation H ` .% `:35 G:34 := rel_droite_mod H


lemma distingue_gde {G:groupe} {H : sous_groupe G} (dH : est_distingue H)
  : (G %. H) = (H .% G) :=
  begin
    unfold rel_droite_mod, 
    rw rel_gauche_mod, unfold est_distingue at dH,
    apply funext, intro, apply funext, intro y,  rw dH, 
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
  (dH : est_distingue H) : (G %. H) = (H .% G)
  := sorry

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
  rw ← dH (a*b) at af, cases af with h₆ a₆, cases a₆ with a₆ eq₄, 
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
def x (G : groupe) (H : sous_groupe G) := G/.H 

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

local notation `⟦`:max a`⟧@`:0 H := quot.mk (rel_gauche_mod H) a 

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

def groupe_quotient {G : groupe} (H : sous_groupe G) (dH : est_distingue H) : groupe :=
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


section

-- Pour définir l'ordre, (∃ n : ℕ, x^(n:ℤ) = 1) n'est pas une proposition décidable en général
-- Il faut donc utiliser le module classical pour que toutes les propositions soient décidables
open classical
local attribute [instance, priority 10] prop_decidable

def ordre_fini {G : groupe} (x : G) : Prop := (∃ n : ℕ, n≠0 ∧ x^(n:ℤ) = 1)

/-
On définit l'ordre d'un élément comme étant égal à :
  - Le plus petit n ∈ N* qui vérifie x^n = 1 si un tel n existe
  - 1 sinon
Cette définition n'est jamais à utiliser directement, et le lemme qui
vient après est celui qui nous permettra de travailler avec les ordres.
-/
noncomputable def ordre {G : groupe} (x : G) : ℕ :=
  if h : ordre_fini x then nat.find h else 0


lemma carac_ordre {G : groupe} (x : G) 
  : (x ^ (ordre x) = 1 ∧ ∀ k : ℕ, k ≠ 0 ∧ k < ordre x → x^k ≠ 1) :=
begin
  by_cases (ordre_fini x),
  { -- ==>
    have h₁ : (ordre x = nat.find h),
      unfold ordre, 
      exact simp_dite h,
    split,
    have h₂ := nat.find_spec h, rw  [←coe_pow_nat, ← h₁] at h₂, exact h₂.2, 
    intros k hk, cases hk with hk1 hk2,
    intro ha,
    rw h₁ at hk2,
    have h₂ := (@nat.find_min _ _ h k) hk2,
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
  have h₃ : (ordre x = nat.find h) := by {unfold ordre, exact simp_dite h},
  rw h₂ at h₃,
  have h₄ := (nat.find_spec h),
  exact h₄.1 h₃.symm, 
end

lemma ordre_fini_est_pos {G : groupe} {x : G} (h : ordre_fini x) : ordre x > 0 :=
  nat.lt_of_le_and_ne (nat.zero_le _) (ordre_fini_est_non_nul h).symm

def singleton_generateur {G : groupe} (x : G) : Prop :=
  @sous_groupe_engendre G {x} = set.univ

def est_cyclique (G : groupe ) := 
  ∃ x : G, singleton_generateur x


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
      revert g, 
      have h_pos : ∀ g : G, ∀ n : ℕ, g = x ^ n → g ∈ sous_groupe_engendre ({x}:set G),
      {
        intros g n hn, revert g, 
        induction n with d hd,
          { -- x^0 = neutre ∈ <x>  
            intros g hk, 
            rw [pow_zero_eq_one] at hk,
            rw hk, 
            exact (engendre_est_sous_groupe ({x}:set G)).2.2,
          },
          { -- x^d avec d ≥ 1 
            intros g hk, 
            have h₀ := hd (x ^ (int.of_nat d)) rfl,
            rw [coe_pow_nat, int.coe_nat_succ, mul_right_pow x] at hk,
            rw ← int.coe_nat_eq at h₀,
            have h₁ : x∈(sous_groupe_engendre ({x}:set G)),
              rw engendre₂_est_engendre, 
              have : x∈ ({x} : set G), unfold has_mem.mem, unfold singleton, unfold set_of, 
              exact ((engendre₂_contient_ens {x}) x this),
              rw hk,
            exact ((engendre_est_sous_groupe {x}).2.1 _ h₀ _ h₁), 
          }
      },
      induction k with n hn, 
      {
        rw ← int.coe_nat_eq, rw ← coe_pow_nat,
        intros g hg, 
        exact h_pos g n hg,
      },
      {
        intros g hk,
        unfold pow at hk, unfold puissance_z at hk, -- TODO: lemme x^(-n) = (x^n)⁻¹
        have h : x ^ (hn + 1) ∈ sous_groupe_engendre ({x}:set G), 
          apply h_pos (x^(hn + 1)) (hn + 1), refl, 
        rw hk,  
        exact ((engendre_est_sous_groupe {x}).1 _ h), 
      }
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



@[instance]
noncomputable def engendre_fini_de_ordre_fini {G : groupe} {x : G} 
  (h : ordre_fini x) : est_fini {g // g ∈ @sous_groupe_engendre G {x}} :=
{
  majorant := ordre x,
  f := λ g, 
    let f_g := choose ((carac_engendre_singleton_ordre_fini h g.val).1 g.property) in
    ⟨int.nat_abs f_g.val, 
      begin
        have h₁ := int.eq_coe_of_zero_le f_g.property.1, cases h₁ with n h₁,
        have h₂ := f_g.property.2.1,
        rw h₁ at *,
        rw int.coe_nat_lt_coe_nat_iff at h₂, 
        rw int.nat_abs_of_nat,
        exact h₂ 
      end
    ⟩,
  f_inj :=
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
  end
}


@[instance]
noncomputable def cyclique_fini_de_ordre_fini {G : groupe} {x : G} 
  (h : ordre_fini x) (h₁ : singleton_generateur x) : est_fini G :=
  @fini_bij_fini {g // g ∈ @sous_groupe_engendre G {x}} (engendre_fini_de_ordre_fini h) G
    (λ g, ⟨g, by {unfold singleton_generateur at h₁, rw h₁, apply true.intro}⟩)
    begin {intro, intro, simp, intro aa, exact aa} end


--set_option trace.class_instances true 

lemma card_groupe_cyclique_fini {G : groupe} {x : G}
  (h₂ : ordre_fini x) (h₁ : singleton_generateur x) [h₃ : est_fini G]
  : cardinal G = ordre x :=


--lemma card_groupe_cyclique {G : groupe} (h: est_cyclique G)
--  : cardinal (G)-/

end
/-******************************Fin Définitions et coercions de base *****************************-/







theorem mor_neutre_est_neutre {G H : groupe} {f : morphisme G H} : f 1 = 1 :=
  sorry

theorem mor_inv_inv_mor {G H : groupe} {f : morphisme G H}  (a : G) : f a⁻¹ =  (f a)⁻¹ :=
  begin
  apply inv_unique,
  --rw ← morphisme.resp_mul f a⁻¹ a, 
  --faut juste que ⇑f soit compris comme f.mor et c'est bon
  sorry
  end


def est_isomorphisme {G H : groupe} (f : morphisme G H) : Prop :=
  ∃ (g : morphisme H G), g.mor ∘ f.mor = id ∧ f.mor ∘ g.mor = id

def End (G : groupe) := morphisme G G
structure Aut (G : groupe) :=
  (f: morphisme G G)
  (h: est_isomorphisme f)

def aut_int {G: groupe} (g : G) : morphisme G G :=
  { mor:= λ h, g*h*g⁻¹,
    resp_mul := 
    begin
    intro a,
    intro b,
    rw ← mul_assoc' G (g*a*g⁻¹) (g * b) g⁻¹,
    rw ←  mul_assoc' G (g*a*g⁻¹) g  b,
    rw mul_assoc' G (g*a) g⁻¹ g,
    rw inv_gauche',
    rw neutre_droite',
    rw mul_assoc' G g a b,    
    end
  }
    

lemma aut_int_est_iso {G: groupe} (g : G) : est_isomorphisme (aut_int g) :=
  sorry

def Int (G: groupe) := {f // ∃ g:G , f = aut_int g } 

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