




section

universe u
 


/-*******************************Définitions et coertions de base ******************************-/

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
Coertions pour simplifier la notation : 
- Avec un groupe G, on peut écrire a : G au lieu de a : G.ens
- Avec deux éléments a, b : G.ens, on peut écrire a*b au lieu de G.mul a b
- Avec un élément a : G.ens, on peut écrire a*1 au lieu de a*G.neutre
- Enfin, avec un élément a : G.ens, on peut écrire a⁻¹ (tapé a\-1) au lieu de G.inv a 
-/
instance groupe_to_ens : has_coe_to_sort groupe (Type u) :=
  ⟨λ a : groupe, a.ens⟩

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
  (mul_stab : ∀ a b ∈ sous_ens, G.mul a b ∈ sous_ens)
  (inv_stab : ∀ a ∈ sous_ens, a⁻¹ ∈ sous_ens)
  (contient_neutre : G.neutre ∈ sous_ens )


/-
Coertion permettant de voir un sous groupe d'un groupe G comme étant lui même
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
  begin -- Constuction du groupe
    let ss_type := {a : G.ens // a ∈ SG.sous_ens}, -- .ens
    let new_mul : ss_type → ss_type → ss_type :=  -- .mul
      λ x y, ⟨x.val*y.val, SG.mul_stab x.val x.property y.val y.property⟩,
    let new_inv : ss_type → ss_type, intro x, -- .inv
      split, 
      show G.ens, from x⁻¹, 
      exact SG.inv_stab x.val x.property,
      have hs : ∀ x y  : ss_type, 
        new_mul x y = ⟨x.val*y.val, SG.mul_stab x.val x.property y.val y.property⟩,
      intros, refl,
      have h_sep : ∀ u v: G.ens, ∀ hp : (u*v) ∈ SG.sous_ens, (⟨u*v,hp⟩:ss_type).val = u*v,
      intros, refl,
    apply groupe.mk ss_type new_mul ⟨G.neutre, SG.contient_neutre⟩ new_inv,
      intros,
      -- 1) Preuve que la restriction de la multiplication reste associative:
        rw (hs a b), rw hs b c,  rw hs _ c, rw hs a _,
        -- Utiliser rw h_sep ne marche pas ici, je n'arrive pas encore à la comprendre pourquoi mais 
        -- voici une explication : https://proofassistants.stackexchange.com/a/1063
        simp only [h_sep] {single_pass := tt},
        exact G.mul_assoc a.val b.val c.val,
      
      -- 2) Preuve que l'élement neutre est toujours neutre 
      intro, rw hs _, simp only [h_sep] {single_pass := tt},
      have wow : G.neutre*x.val = G.mul G.neutre x.val, refl, simp only [wow] {single_pass := tt},--why?
      simp only [G.neutre_gauche] {single_pass := tt},
      apply subtype.eq, refl,
      
      -- 3) Preuve que (inv x) * x = neutre est toujours vraie
      intro, rw hs, rw subtype.mk.inj_eq, 
      have hh : (new_inv x).val = (G.inv x.val), refl,
      rw hh, have : G.inv x.val * x.val = G.mul (G.inv x.val) x.val, refl, rw this, 
      rw G.inv_gauche _,  
  end
  ⟩

--instance sous_groupe_to_sous_type {G: groupe} :
 -- has_coe_to_sort (sous_groupe G) (Type u) := 
  --⟨λ H: sous_groupe G, {a // H.sous_ens a}⟩



section 

variable (G: groupe)
variable (H: sous_groupe G)
variable (a : G)
variable (b : {c // H.sous_ens c})
variable (b' : (@coe_sort.{u+1 u+2} (sous_groupe G) (Type u)
    (@coe_sort_trans.{u+2 u+1 u+2} (sous_groupe G) groupe (Type u) groupe_to_ens
       (@coe_base_aux.{u+1 u+2} (sous_groupe G) groupe (@sous_groupe_to_groupe G)))
    H))

#reduce (@coe_sort.{u+1 u+2} (sous_groupe G) (Type u)
    (@coe_sort_trans.{u+2 u+1 u+2} (sous_groupe G) groupe (Type u) groupe_to_ens
       (@coe_base_aux.{u+1 u+2} (sous_groupe G) groupe (@sous_groupe_to_groupe G)))
    H)

#reduce a*b -- works
#reduce a*(b') -- does not work 

end

set_option pp.all true
example (G: groupe) (H : sous_groupe G) (a : G) (b : H): G.ens := G.mul a b

/-******************************Fin Définitions et coertions de base *****************************-/





-- permet d'avoir accès à tous les théorèmes sous le même nom que la structure
-- permet également de "cacher" nos noms de théorèmes pour éviter les conflits 
namespace groupe 

theorem neutre_droite {G : groupe} : ∀ a : G.ens, a*1 = a :=
 sorry

theorem inv_droite {G: groupe} : ∀ a : G.ens, a * (G.inv a) = 1 :=
  sorry


theorem neutre_unique {G: groupe} (e : G.ens) (h : ∀ a, e*a = a ) : e = 1 :=
  begin
  have h1 := h 1,
  rw neutre_droite at h1,
  rwa h1,
  end

theorem inv_unique {G: groupe} (a : G.ens) (b : G.ens) (h: b*a = 1) : b = G.inv a :=
  sorry

inductive ordre 
  | entier : ℕ → ordre  
  | infini : ordre

def puissance {G: groupe} (x : G.ens) (n : ℕ ) : G.ens :=
  begin
    induction n with m hm,
    exact G.neutre, -- si c'est 0
    exact hm*x, -- si c'est m+1 avec x^m = hm
  end 



structure morphisme (G H : groupe) :=
  (mor : G.ens → H.ens)
  (resp_mul : ∀ a b : G.ens, mor (a*b) = (mor a) * (mor b) )


theorem mor_neutre_est_neutre {G H : groupe} {f : morphisme G H} : f.mor G.neutre = H.neutre :=
  sorry

theorem mor_inv_inv_mor {G H : groupe} {f : morphisme G H}  (a : G.ens) : f.mor (G.inv a) = H.inv (f.mor a) :=
  sorry


def ker {G H : groupe} (f : morphisme G H) : set G.ens :=
  {a : G.ens | f.mor a = H.neutre}

def im {G H : groupe} (f : morphisme G H) : set H.ens :=
  {b : H.ens | ∃ a : G.ens, f.mor a = b }

def ens_reciproque {G H : groupe} (f : morphisme G H) (B: set H.ens) :=
  {a : G.ens | f.mor a ∈ B }

def ens_image {G H : groupe} (f : morphisme G H) (A: set G.ens) :=
  {b : H.ens | ∃ a ∈ A, f.mor a = b}

def comp {G H K: groupe} (f : morphisme G H) (g : morphisme H K) : morphisme G K := 
  sorry


theorem ker_comp_eq_inv_ker {G H K: groupe} (f : morphisme G H) (g : morphisme H K) 
  : ker (comp f g) = ens_reciproque f (ker g) :=
  sorry

theorem im_comp_eq_im_im {G H K: groupe} (f : morphisme G H) (g : morphisme H K) 
  : im (comp f g) = ens_image g (im f) :=
  sorry 


def isomorphisme {G H: groupe } (f : morphisme G H) :=
  ∃ g : morphisme H G, (∀ a : G.ens,  g.mor (f.mor a) = a)



end groupe


end