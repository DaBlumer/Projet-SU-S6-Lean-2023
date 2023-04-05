


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

lemma eq_in_ss_groupe_iff_eq {G : groupe} {H : sous_groupe G} (a b : H)
  : ((a:G) = ↑b) ↔ (a = b) :=
begin
  split; intro p; try {rw p},
  unfold coe at p, unfold lift_t at p, unfold has_lift_t.lift at p,
  unfold coe_t at p, unfold has_coe_t.coe at p, unfold coe_b at p,
  unfold has_coe.coe at p, apply subtype.eq, exact p,
end


-- Définition d'un morphisme de groupes
structure morphisme (G H : groupe) :=
  (mor : G → H)
  (resp_mul : ∀ a b : G, mor (a*b) = (mor a) * (mor b) )

-- Permet de voir un morphisme comme l'application sous-jacente quand c'est nécessaire
instance morphisme_to_fonction {G H : groupe}
  : has_coe_to_fun (morphisme G H) (λ _, G → H) :=
  ⟨λ m, m.mor⟩

def comp_mor {G H K: groupe} (g : morphisme H K) (f : morphisme G H) : morphisme G K := 
  {
    mor := g.mor∘f.mor,
    resp_mul := λ g₁ g₂, by {simp, rw [f.resp_mul, g.resp_mul]} 
  }

local notation g `∘₁`:10 f := comp_mor g f

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

lemma neutre_unique_fort (G : groupe) (e a : G) (h : e*a = a) : e = 1 :=
  by {rw [mul_droite_div_droite, inv_droite] at h, exact h}


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

lemma x_pow_in_sous_groupe {G: groupe} {x : G} {A : set G} {h : est_sous_groupe A}
  : x∈A → ∀ k : ℤ, x^k ∈ A :=
begin
  intros h₃ k,
  have result_for_nat : ∀ n : ℕ, x^n ∈ A,
    intro n, induction n with n hn, 
    rw pow_zero_eq_one, exact h.2.2,
    rw [coe_pow_nat,int.coe_nat_succ,mul_right_pow],
    rw coe_pow_nat at hn,
    exact h.2.1 _ hn _ h₃, 
  cases k,
    rw [← int.coe_nat_eq, ←coe_pow_nat], exact result_for_nat _,
    rw [← int.neg_of_nat_of_succ, pow_minus_eq_inv_pow],
    apply h.1,
    exact result_for_nat _,
end

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


local notation a ` *₂ `:51 H:51 :=  mul_gauche_ens a H
local notation H ` *₃ `:51 a:51 := mul_droite_ens H a

def est_distingue {G : groupe} (H : sous_groupe G) : Prop :=
  ∀ a:G, a *₂ H = H *₃ a


lemma carac_est_distingue {G : groupe} (H' : sous_groupe G)
  : est_distingue H' ↔ ∀ h ∈ H', ∀ g : G, g*h*g⁻¹ ∈ H'  :=
begin
  split, {
    intros dis_H h h_in_H g,
    unfold est_distingue at dis_H,
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
    intro P, intro g,
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

lemma distingue_droite_to_gauche {G : groupe } {H' : sous_groupe G}
  (dH : est_distingue H') (h ∈ H') (g : G) : ∃ h' ∈ H', g*h = h'*g :=
begin
  apply Exists.intro (g*h*g⁻¹),
  apply Exists.intro ((carac_est_distingue H').1 dH _ H g),
  repeat {rw mul_assoc'}, rw [inv_gauche', neutre_droite],
end

def rel_gauche_mod {G : groupe} (H : sous_groupe G) : G → G → Prop :=
  λ x y : G, y ∈ x *₂ H 
def rel_droite_mod {G : groupe} (H : sous_groupe G) : G → G → Prop :=
  λ x y : G, y ∈ ↑H *₃ x 

local notation G ` %. `:35 H:34 := rel_gauche_mod H
local notation H ` .% `:35 G:34 := rel_droite_mod H


lemma distingue_gde {G:groupe} {H : sous_groupe G} (dH : est_distingue H)
  : (G %. H) = (H .% G) :=
  begin
    unfold rel_droite_mod, 
    rw rel_gauche_mod, unfold est_distingue at dH,
    apply funext, intro, apply funext, intro y,  rw dH, 
  end

lemma rel_gauche_carac₁ {G : groupe} (H : sous_groupe G) (a b : G)
  : rel_gauche_mod H a b ↔ a *₂ H = b *₂ H :=
begin
  split; intro p, {
    cases p with h tmp, cases tmp with h_H b_ah,
    rw ←set_eq, intro g,
    split;intro g_in; cases g_in with h₂ tmp; cases tmp with h₂_H g_ab_h, {
      have p := b_ah.symm, rw [mul_droite_div_droite] at p, rw p at g_ab_h,
      existsi h⁻¹*h₂, existsi H.mul_stab _ (H.inv_stab _ h_H) _ h₂_H,
      rw [g_ab_h, mul_assoc'],
    }, {
      rw b_ah at g_ab_h,
      existsi h*h₂, existsi H.mul_stab _ h_H _ h₂_H,
      rw [g_ab_h, mul_assoc'],
    }
  }, {
    unfold rel_gauche_mod, rw p, 
    existsi [(1:G), H.contient_neutre],
    rw neutre_droite, 
  }
end

lemma rel_gauche_carac₂ {G : groupe} (H : sous_groupe G) (a b : G) {h h' : H}
  (p : a*h = b*h') : rel_gauche_mod H a b :=
begin
  have p' := p.symm,
  rw [mul_droite_div_droite, mul_assoc'] at p',
  existsi ((h:G)*(h':G)⁻¹), existsi (H.mul_stab _ h.property _ (H.inv_stab _ h'.property)), 
  exact p',
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
  (dH : est_distingue H) : (G %. H) = (H .% G) :=
begin
  unfold rel_gauche_mod, unfold rel_droite_mod,
  apply funext,
  intro, apply funext, intro, 
  rw dH,
end

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
 
local notation `⟦`:max a`⟧@`:max H := quot.mk (rel_gauche_mod H) a 

def classes_equiv_gauche {G : groupe} (H : sous_groupe G) :=
  {X // ∃ a : G, X = mul_gauche_ens a H}

def elem_to_classe_gauche {G : groupe} (H : sous_groupe G)
  (x : G) : classes_equiv_gauche H := 
{
  val := mul_gauche_ens x H,
  property := by {apply Exists.intro x, refl,}
}

lemma e_to_cg_resp_rel {G : groupe} (H : sous_groupe G) (a b : G) (a_b : (G %. H) a b) 
  : elem_to_classe_gauche H a = elem_to_classe_gauche H b :=
begin
  unfold elem_to_classe_gauche,
  apply subtype.eq, simp, 
  rw ← rel_gauche_carac₁, exact a_b,
end

def quot_to_classe_gauche {G : groupe} (H : sous_groupe G) : (G/.H) → classes_equiv_gauche H :=
  quot.lift (elem_to_classe_gauche H) (e_to_cg_resp_rel H)

def bij_classes_equiv_quot {G : groupe} (H : sous_groupe G)
  : bijection (G /. H) (classes_equiv_gauche H) :=
{
  val := quot_to_classe_gauche H,
  property :=
  begin
    split, { -- Injective
      intros a₁ a₂ p, 
      unfold quot_to_classe_gauche at p,
      cases quot.exists_rep a₁ with g₁ g_a₁,
      cases quot.exists_rep a₂ with g₂ g_a₂,
      rw [←g_a₁, ←g_a₂] at *,
      simp at p,
      unfold elem_to_classe_gauche at p,
      apply quot.sound,
      rw subtype.mk.inj_eq at p,
      rw rel_gauche_carac₁,
      exact p,
    }, { -- Surjective
      intro B, 
      cases B.property with b B_bH,
      existsi (quot.mk _ b),
      unfold quot_to_classe_gauche,
      unfold elem_to_classe_gauche,
      apply subtype.eq, simp,
      rw B_bH,
    }
  end
}

lemma quot_to_classe_gauche_id {G : groupe} (H : sous_groupe G)
  (a : G) : (quot_to_classe_gauche H (quot.mk _ a)).val = a *₂ H := rfl

lemma quot_to_classe_gauche_id₂ {G : groupe} (H : sous_groupe G)
  (a : G) : (quot_to_classe_gauche H (quot.mk _ a)) = ⟨a *₂ H, (quot_to_classe_gauche H (quot.mk _ a)).property⟩ := rfl

lemma quot_to_classe_gauche_prop {G : groupe} {H : sous_groupe G}
  : function.bijective (quot_to_classe_gauche H) := (bij_classes_equiv_quot H).property

noncomputable def repr_quot {G : groupe} {H : sous_groupe G} (a : G/.H) : {g // (⟦g⟧@H) = a} :=
  ⟨choose (quot.exists_rep a), prop_of_choose (quot.exists_rep a)⟩

lemma class_of_repr_quot {G : groupe} {H : sous_groupe G} (a : G/.H)
  : (⟦repr_quot a⟧@H) = a := (repr_quot a).property


lemma quot_gauche_exact {G : groupe} {H : sous_groupe G} (a b : G)
   (p : (⟦a⟧@H) = (⟦b⟧@H)) : rel_gauche_mod H a b :=
begin
  have p' := eq.refl (quot_to_classe_gauche _ (⟦a⟧@H)),
  conv at p' {to_rhs, rw p},
  rw [quot_to_classe_gauche_id₂] at p',
  conv at p' {to_rhs, rw quot_to_classe_gauche_id₂},
  rw subtype.mk.inj_eq at p', 
  rw rel_gauche_carac₁,
  exact p', 
end

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


end
/-******************************Fin Définitions et coercions de base *****************************-/




lemma mor_resp_mul {G H : groupe} {f : morphisme G H}
  : ∀ a b : G, f (a * b) = f a * f b := λ a b, f.resp_mul a b 

lemma mor_fun_eq {G H : groupe} (f : morphisme G H) : (f : G→H) = f.mor := rfl
lemma comp_mor_fun_eq {G H K: groupe} (g : morphisme H K) (f : morphisme G H)
  : (g∘₁f : G→K) = ((g:H→K) ∘ (f:G→H)) := rfl 

lemma mor_neutre_est_neutre {G H : groupe} {f : morphisme G H} : f 1 = 1 :=
begin
  apply H.neutre_unique_fort (f 1) (f 1),
  rw [← mor_resp_mul, G.neutre_droite],
end

theorem mor_inv_inv_mor {G H : groupe} {f : morphisme G H}  (a : G) : f a⁻¹ =  (f a)⁻¹ :=
  begin
  apply inv_unique,
  rw ← mor_resp_mul a⁻¹ a,
  rw inv_gauche',
  rw mor_neutre_est_neutre,
  end


def est_isomorphisme {G H : groupe} (f : morphisme G H) : Prop :=
  ∃ (g : morphisme H G), function.left_inverse g f ∧ function.right_inverse g f

lemma carac_est_isomorphisme {G H : groupe} (f : morphisme G H)
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
      apply Exists.intro (⟨g, inv_resp_mul⟩ : morphisme H G),
      exact ⟨f_bij_inv.inv_gauche, f_bij_inv.inv_droite⟩, 
  }
end

def End (G : groupe) := morphisme G G
def Aut (G : groupe) := {f : morphisme G G // est_isomorphisme f}

def aut_int_fun {G : groupe} (g : G) (h : G) : G := g*h*g⁻¹
def aut_int {G: groupe} (g : G) : morphisme G G :=
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


def im_recip {G H : groupe} (f : morphisme G H) (B: set H) :=
  im_recip (f : G→H) B

def ens_image {G H : groupe} (f : morphisme G H) (A: set G) :=
  im_dir (f : G→H) A

def ker {G H : groupe} (f : morphisme G H) : set G :=
  {a : G.ens | f a = 1}

def im {G H : groupe} (f : morphisme G H) : set H :=
  {b : H | ∃ a : G, f a = b }

-- ↓ Utile pour pruver qu'un élément appartient à l'image
lemma im_point_in_im {G H : groupe} (f : morphisme G H) (x : G)
  : f x ∈ im f := by {apply Exists.intro x, refl}
-- ↓ Utile pour prouver qu'un élément appartient au noyeau
lemma im_one_in_ker {G H : groupe} (f : morphisme G H) (x : G)
  : (f x = 1) = (x ∈ ker f) := rfl
lemma in_ens_image {G H : groupe} (f : morphisme G H) (B : set H) (x : G)
  : (f x ∈ B) = (x ∈ im_recip f B) := rfl 

lemma ker_est_sous_groupe {G H : groupe} (f : morphisme G H)
  : est_sous_groupe (ker f) :=
begin 
  split,
  { -- stabilité de l'inverse
    intros a h, rw ←im_one_in_ker at *,
    rw mor_inv_inv_mor,
    rw h,
    rw [H.mul_droite_all _ _ 1, inv_gauche', neutre_gauche'],
  }, split,
  {
    intros a ha b hb, 
    rw ←im_one_in_ker at *, 
    rw [mor_resp_mul, ha, hb, neutre_droite], 
  },
  exact mor_neutre_est_neutre,
end

lemma im_ss_groupe_est_ss_groupe {G H : groupe} (f : morphisme G H) (G' : sous_groupe G)
  : est_sous_groupe (ens_image f G') := 
begin
  split, {
    intros a tmp, cases tmp with pre_a tmp, cases tmp with a_in a_eq, 
    apply Exists.intro pre_a⁻¹, apply Exists.intro (G'.inv_stab _ a_in),
    rw mor_inv_inv_mor,
    rw eq_of_inv_eq, exact a_eq,
  }, split, {
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

lemma preim_ss_groupe_est_ss_groupe {G H : groupe} (f : morphisme G H) (H' : sous_groupe H)
  : est_sous_groupe (im_recip f H') :=
begin
  split, {
    intros a ha, rw ←in_ens_image at *,
    rw mor_inv_inv_mor,
    exact H'.inv_stab _ ha, 
  }, split, {
    intros a ha b hb, rw ←in_ens_image at *,
    rw mor_resp_mul,
    exact H'.mul_stab _ ha _ hb,
  }, {
    rw [←in_ens_image, mor_neutre_est_neutre], exact H'.contient_neutre,
  }
end

lemma carac_mor_inj {G H : groupe} (f : morphisme G H) 
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

theorem ker_comp_eq_inv_ker {G H K: groupe} (g : morphisme H K) (f : morphisme G H)
  : ker (g ∘₁ f) = im_recip f (ker g) := by {refl} 
-- ↑ Par définition, x ∈ ker (g ∘ f) est égal à x ∈ f⁻¹ (ker g). Lean sait faire seul c: 

theorem im_comp_eq_im_im {G H K: groupe} (f : morphisme G H) (g : morphisme H K) 
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

def centre {G : groupe} : set G := {g | ∀ h, g*h = h*g}


instance ss_gr_fini_de_gr_fini {G : groupe} {H : sous_groupe G} [fG : est_fini G] : est_fini H :=
{
  majorant := fG.majorant, 
  f := λ h, fG.f h,
  f_inj :=
  begin
    intros a a' aa, 
    simp at aa, 
    have p := fG.f_inj aa,
    exact (eq_in_ss_groupe_iff_eq _ _).1 p,
  end
}

noncomputable instance quot_fini_de_gr_fini {G : groupe} {H : sous_groupe G} [fG : est_fini G] : est_fini (G /. H) :=
{
  majorant := fG.majorant,
  f := λ X, fG.f (repr_quot X).val,
  f_inj :=
  begin
    intros A A' AA, simp at AA,
    have p := fG.f_inj AA,
    rw [←(repr_quot A).property, ←(repr_quot A').property],
    rw p, 
  end
}


noncomputable def fun_gr_prod_ss_gr_quot {G : groupe} {H : sous_groupe G} (U : H × (G/.H)) : G
  := repr_quot(U.2)*U.1

/-
Théorème 1.37 du cours
La preuve ici consiste à exhiber une bijection entre G et (H × G/H):
  - On se munit de repr_quot : G/H → G qui nous donne un représentant arbitraire pour chaque classe.
  - On montre que la fonction qui à (h, X) repr_quot(X)*h est une bijection
-/
theorem theoreme_de_lagrange {G : groupe} (H : sous_groupe G) [fG : est_fini G]
  : cardinal G = cardinal H * cardinal (G /. H) :=
begin 
  rw ← prod_of_cards, 
  apply eq_card_of_idempotents, apply bijection_comm,
  exact {
    val := fun_gr_prod_ss_gr_quot, 
    property :=
    begin
      split, { -- Preuve que c'est une injection
        -- On introduit (h, X) et (h', X') tq f(h, X) = f(h', X')
        intros a a',
        cases a with h X, cases a' with h' X',
        intro aa,
        unfold fun_gr_prod_ss_gr_quot at aa, 

        -- On montre que repr(X) et repr(X') sont équivalents et que donc X = X'
        have aa_equiv : (⟦repr_quot X⟧@H)= (⟦repr_quot X'⟧@H),
          apply quot.sound,
          apply rel_gauche_carac₂,
          exact aa, 
        repeat {rw class_of_repr_quot at aa_equiv},
        
        -- On montre que h = h'
        rw aa_equiv at *, 
        rw ←mul_gauche_all at aa, 
        simp at aa, rw eq_in_ss_groupe_iff_eq at aa,
        rw aa, 
      }, { -- Preuve que c'est une surjection
        intro, 
        let x := repr_quot(⟦b⟧@H),
        have p : rel_gauche_mod H x b,
          exact quot_gauche_exact _ _ x.property,
        cases p with h hp, cases hp with h_H ph,
        existsi (⟨⟨h, h_H⟩, ⟦b⟧@H⟩ : H × (G/.H)),
        
        have why : ∀ x y, fun_gr_prod_ss_gr_quot ⟨x, y⟩ = (repr_quot y)*x := λ x y, rfl, 
        rw why,

        conv {to_rhs, rw ph},
        have why₂ : ((⟨h, h_H⟩:H):G) = h := rfl, rw why₂,
      }
    end
  }
end

end groupe


end