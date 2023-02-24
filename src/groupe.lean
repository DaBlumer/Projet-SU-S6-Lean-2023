

-- première version


section

universe u
 

structure groupe : Type (u+1) :=
  (ens : Type u)
  (mul : ens → ens → ens )
  (neutre : ens)
  (inv : ens → ens )
  (mul_assoc : ∀ a b c : ens, mul (mul a b) c = mul a (mul b c))  
  (neutre_gauche : ∀ x : ens, mul neutre x = x)
  (inv_gauche : ∀ x : ens, mul (inv x) x = neutre)

instance groupe_has_mul (G : groupe) :
  has_mul (G.ens) := ⟨G.mul⟩

instance groupe_has_one (G: groupe) :
  has_one (G.ens) := ⟨G.neutre⟩


--instance groupe_to_ens : has_coe_to_sort groupe :=
--{S := Type u, coe := λ S, S.ens}

structure sous_groupe (G: groupe) :=
  (sous_ens : set G.ens)
  (mul_stab : ∀ a b ∈ sous_ens, G.mul a b ∈ sous_ens)
  (inv_stab : ∀ a ∈ sous_ens, G.inv a ∈ sous_ens)
  (contient_neutre : G.neutre ∈ sous_ens )


/--def sous_type (G:groupe) (sg : sous_groupe G) := { x : G.ens // x ∈ sg.sous_ens }

def mul_sg (G: groupe) (SG : sous_groupe G) (a b : sous_type G) :=



instance sous_groupe_to_groupe {G: groupe }:
  has_coe (sous_groupe G) groupe :=
  (λ sg : sous_groupe G, 
    let sous_type :=  in
    let mul_sg := λ x : sous_type, λ y : sous_type, 
       sous_type.mk  (G.mul x.val y.val) (sg.mul_stab x y 
    begin
      apply groupe.mk { x : G.ens // x ∈ sg.sous_ens } 
     
      
    end
  )
--/
def a := 2



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