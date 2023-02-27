




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

/-******************************Fin Définitions et coercions de base *****************************-/





-- permet d'avoir accès à tous les théorèmes sous le même nom que la structure
-- permet également de "cacher" nos noms de théorèmes pour éviter les conflits 
namespace groupe 

theorem neutre_droite {G : groupe} : ∀ a : G.ens, a*1 = a :=
 sorry

theorem inv_droite {G: groupe} : ∀ a : G.ens, a * a⁻¹ = 1 :=
  sorry


theorem neutre_unique {G: groupe} (e : G.ens) (h : ∀ a, e*a = a ) : e = 1 :=
  begin
  have h1 := h 1,
  rw neutre_droite at h1,
  rwa h1,
  end

theorem inv_unique {G: groupe} (a : G.ens) (b : G.ens) (h: b*a = 1) : b = a⁻¹ :=
  sorry

inductive ordre 
  | entier : ℕ → ordre  
  | infini : ordre

def puissance {G: groupe} (x : G) (n : ℕ ) : G :=
  begin
    induction n with m hm,
    exact G.neutre, -- si c'est 0
    exact hm*x, -- si c'est m+1 avec x^m = hm
  end 





theorem mor_neutre_est_neutre {G H : groupe} {f : morphisme G H} : f 1 = 1 :=
  sorry

theorem mor_inv_inv_mor {G H : groupe} {f : morphisme G H}  (a : G) : f a⁻¹ =  (f a)⁻¹ :=
  sorry


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