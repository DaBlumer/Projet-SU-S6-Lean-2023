import .generique
import .cardinalite_finie
import base
import distingue
import sous_groupes
import morphismes
open generique


namespace groupe

/-****************************************Ensemble quotient et groupe quotient ****************************************-/
/-
- Définitions principales :
  - rel_gauche_mod et rel_droite_mod : les deux relations d'équivalence modulo un sous groupe
    - Notation utilisée : G%.H pour rel_gauche_mod et H.%G pour rel_droite_mod
  - quotient_gauche et quotient_droite : les deux types quotient
    - Notation utilisée : G /. H pour quotient_gauche et H .\ G pour quotient_droite
  - groupe_quotient : si H ⊲ G, le groupe quotient de G sur H
    - Notation utilisée : G /* H
  - mor_quotient : le morphisme naturel de G vers G/*H qui renvoie chaque élément à sa classe
  - repr_quot : application de G/*H vers G qui associe à chaque classe un représentant arbitraire.
- Notations introduites : 
  - G%.H et H.%G pour les deux relations d'équivalence
  - G /* H pour le groupe quotient
  - ⟦a⟧@H pour la classe d'équivalence de a modulo H. ⟦a⟧ s'écrit \[[a\]] 
-/


-- ↓ ↓ ↓ On définit les deux relations d'équivalence et leurs notations 
def rel_gauche_mod {G : groupe} (H : sous_groupe G) : G → G → Prop :=
  λ x y : G, y ∈ x *₂ H 
def rel_droite_mod {G : groupe} (H : sous_groupe G) : G → G → Prop :=
  λ x y : G, y ∈ ↑H *₃ x 

notation G ` %. `:35 H:34 := rel_gauche_mod H
notation H ` .% `:35 G:34 := rel_droite_mod H


-- Si H est distingué dans G, les deux relations sont les mêmes
lemma distingue_gde {G:groupe} (H : sous_groupe G) [dH : H ⊲ G]
  : (G %. H) = (H .% G) :=
  begin
    unfold rel_droite_mod, 
    rw rel_gauche_mod, unfreezingI{cases dH},
    apply funext, intro, apply funext, intro y,  rw dH, 
  end


-- ↓ ↓ ↓ Deux éléments a et b sont équivalents mod H ssi aH = bH
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
-- ↓ ↓ ↓ Si on a a*h = b*h' pour h et h' dans H, alors a et b sont équivalents mod H
lemma rel_gauche_carac₂ {G : groupe} {H : sous_groupe G} {a b : G} {h h' : H}
  (p : a*h = b*h') : rel_gauche_mod H a b :=
begin
  have p' := p.symm,
  rw [mul_droite_div_droite, mul_assoc'] at p',
  existsi ((h:G)*(h':G)⁻¹), existsi (H.mul_stab _ h.property _ (H.inv_stab _ h'.property)), 
  exact p',
end


/-
↓ ↓ ↓ Lemmes montrant que la relation à gauche est une relation d'équivalence ↓ ↓ ↓  
-/
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



-- Lemme montrant que si H est distingué, alors la relation d'équivalence à gauche est compatible avec la multiplication
-- Autrement dit si a ≣ c [H] et b ≣ d [H], alors a*b ≣ c*d [H]
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
  rw ← dH.h (a*b) at af, cases af with h₆ a₆, cases a₆ with a₆ eq₄, 
  rw eq₄ at eq₁, 
  apply Exists.intro h₆, apply Exists.intro a₆, assumption,  
end  


/-
↓ ↓ ↓ On définit les deux ensembles quotients et leurs notations ↓ ↓ ↓
- On utilise ici 'quot' qui est un outil de la base logique de Lean définissant le type quotient
d'un type α par une relation r sur α (sans nécessiter que r soit une relation d'équivalence)
- Le type quotient produit est le quotient de α par la relation d'équivalence engendrée par r
  (c'est à dire la plus petite relation d'équivalence contenant r)
- Dans notre cas, (G %.H) est déjà une relation d'équivalence, il suffit alors de montrer le lemme
  quot_gauche_exact qui vient plus bas, qui garantit que si deux éléments ont la même classe, alors ils 
  sont équivalents.
-/
def quotient_gauche {G : groupe} (H : sous_groupe G) 
  := quot (G %. H)
def quotient_droite {G : groupe} (H : sous_groupe G)
  := quot (H .% G)

instance g_has_quotient_gauche {G: groupe}  : has_quotient_gauche G (sous_groupe G)
  := ⟨λ H, quotient_gauche H⟩
instance g_has_quotient_droite {G: groupe} : has_quotient_droite G (sous_groupe G)
  := ⟨λ H, quotient_droite H⟩
 

 -- Notation pour avoir la classe de a modulo H : ⟦a⟧@H
notation `⟦`:max a`⟧@`:max H:max := quot.mk (rel_gauche_mod H) a 


/- ↓ ↓ ↓ ↓ ↓ ↓ ↓ ↓ ↓ ↓ ↓ ↓ ↓ ↓ ↓
- Partie dans laquelle on fait le lien entre le type quotient tel que défini dans Lean, et la représentation en
ensemble de classes telle qu'on utilise en mathématiques classiques.
- On établit une bijection entre le type quotient (G/.H) et le type des ensembles de la forme gH.
- Cette partie n'est utilisée nulle part ailleurs dans la suite.
-/

-- On définit le type des classes(ensembles)
def classes_equiv_gauche {G : groupe} (H : sous_groupe G) :=
  {X // ∃ a : G, X = mul_gauche_ens a H}

-- Fonction qui associe à chaque élément g sa classe(ensemble) gH
def elem_to_classe_gauche {G : groupe} (H : sous_groupe G)
  (x : G) : classes_equiv_gauche H := 
{
  val := mul_gauche_ens x H,
  property := by {apply Exists.intro x, refl,}
}


-- On montre que cette représentation respecte bien la relation d'équivalence
lemma e_to_cg_resp_rel {G : groupe} (H : sous_groupe G) (a b : G) (a_b : (G %. H) a b) 
  : elem_to_classe_gauche H a = elem_to_classe_gauche H b :=
begin
  unfold elem_to_classe_gauche,
  apply subtype.eq, simp, 
  rw ← rel_gauche_carac₁, exact a_b,
end

/-
- On définit ici une bijection entre les deux représentations
- On utilise quot.lift qui nous permet, grâce au fait que cette représentation respecte la relation,
  de définir la fonction qui va de G/.H vers le type des classes qui respecte la fonction elem_to_classe_gauche.
  --> C'est ce qu'on fait d'habitude en posant une définition de la sorte en ayant f : G → X
                            F :  G/H → X
                                 ⟦g⟧ ↦ f(g)
      et on dit que F est bien définie car pour g et g' ayant la même classe, f(g) = f(g')
    Ce procédé est exactement la fonction quot.lift sur Lean. Son premier argument est la fonction f, et son second
    est une preuve que f(g)=f(g') pour tous g g' ayant la même classe
-/
def quot_to_classe_gauche {G : groupe} (H : sous_groupe G) : (G/.H) → classes_equiv_gauche H :=
  quot.lift (elem_to_classe_gauche H) (e_to_cg_resp_rel H)
-- ↓ On montre que la fonction définie ci-dessus est bien une bijection.
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

-- ↓ Par définition, notre bijection associe à ⟦a⟧@H l'ensemble aH
lemma quot_to_classe_gauche_id {G : groupe} (H : sous_groupe G)
  (a : G) : (quot_to_classe_gauche H (quot.mk _ a)).val = a *₂ H := rfl
-- ↓ On énonce le même lemme que précédemment sous une forme différente
lemma quot_to_classe_gauche_id₂ {G : groupe} (H : sous_groupe G)
  (a : G) : (quot_to_classe_gauche H (quot.mk _ a)) = ⟨a *₂ H, (quot_to_classe_gauche H (quot.mk _ a)).property⟩ := rfl
-- ↓ On fait un lemme à part pour dire que c'est une bijection
lemma quot_to_classe_gauche_prop {G : groupe} {H : sous_groupe G}
  : function.bijective (quot_to_classe_gauche H) := (bij_classes_equiv_quot H).property
/-
FIN de la partie établir une bijection entre les deux représentations
-/


/-
Fonction importante : nous donne un représentant quelquonque pour chaque classe d'équivalence.
  --> noncomputable car en faisant un choix quelquonque, on doit utiliser des axiomes de classical
-/
noncomputable def repr_quot {G : groupe} {H : sous_groupe G} (a : G/.H) : {g // (⟦g⟧@H) = a} :=
  ⟨choose (quot.exists_rep a), prop_of_choose (quot.exists_rep a)⟩
-- ↓ Par définition, la classe d'un représentant est lui même
lemma class_of_repr_quot {G : groupe} {H : sous_groupe G} (a : G/.H)
  : (⟦repr_quot a⟧@H) = a := (repr_quot a).property


/-
Lemme important : établissant que le type quotient G/.H est bien le quotient de G par la relation d'équivalence G%.H
Si a et b ont la même classe, alors ils sont équivalents
-/
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


/- ↓ ↓ ↓ ↓ ↓ ↓ ↓ ↓ ↓ ↓ ↓ ↓ ↓ ↓ ↓ ↓ ↓ ↓ ↓ ↓ ↓ ↓ 
- Dans cette partie, on définit en deux étapes la multiplication dans le groupe quotient, en utilisant encore une fois quot.lift
    - On définit d'abord mul_partielle_gauche_ : G×G → G/.H qui associe simplement à a et b la classe de a*b
    - On lift une fois pour obtenir mul_partielle_gauche_quotient_ : G×(G/H) → (G/H) définie par :
                        (a, ⟦b⟧) ↦ mul_partielle_gauche_ a b
      et qui est bien définie car pour tous b b' équivalents, mul_partielle_gauche_ a b = mul_partielle_gauche_ a b'
    - On lift une seconde fois pour obtenir mul_quotient_ : (G/H) × (G/H) → (G/H), la vraie multiplication, définie par 
                        (⟦a⟧, ⟦b⟧) ↦ mul_partielle_gauche_quotient_ a b
      et qui est encore une fois bien définie car mul_partielle_gauche_quotient_ est compatible avec la relation d'équivalence
- On définit ensuite l'inverse, qui est défini en faisant un lift une seule fois à partir de la fonction inverse de G 
-/

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
      rw distingue_gde H, assumption, 
    have : (G %. H) a⁻¹ b⁻¹, 
      exact rel_gauche_symm H b⁻¹ a⁻¹ t₁, 
    exact quot.sound this, 
  end
  )
/-
FIN des définitions de la multiplication et de l'inverse dans G/*H
-/

-- Propriété vérifiée par définition : ⟦a⟧*⟦b⟧ = ⟦a*b⟧
lemma quot_of_mul_quot {G: groupe} {H: sous_groupe G} {dH : est_distingue H}
  : ∀ a b : G, mul_quotient_ dH (⟦a⟧@H) (⟦b⟧@H) = ⟦a*b⟧@H := λ a b, rfl
-- ↓ Analogue à repr_quot X, existe_repr_of_quot X est une preuve d'existence d'un représentant, sans pour autant en fournir un
lemma existe_repr_of_quot {G : groupe} {H : sous_groupe G}
  : ∀ X : (G/.H), ∃ x : G, X = (⟦x⟧@H) :=
begin
  have : ∀ a : G, ∃ x : G, (⟦a⟧@H) = (⟦x⟧@H), intro, apply Exists.intro a, refl,
  intro X, 
  exact quot.ind this X, 
end


/-
Définition du groupe quotient G/*H et notation pour celui ci, ainsi que du morphisme naturel G → G/H
-/
def groupe_quotient {G : groupe} (H : sous_groupe G) [dH : est_distingue H] : groupe :=
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


notation G ` /* `:61 H:61 := @groupe_quotient G H _

-- Conversion automatique depuis l'ensemble (le type) quotient et sa structure de groupe associée
instance ens_quot_to_groupe_quot {G : groupe } {H : sous_groupe G} [H ⊲ G] : has_coe (G/.H) (G/*H)
  := ⟨id⟩

-- On définit (et montre que c'est un morphisme) le morphisme de classe G → G/H
def mor_quotient {G : groupe} (H : sous_groupe G) [dH: est_distingue H] : morphisme G (G/*H) :=
{
  mor := λ g, ⟦g⟧@H,
  resp_mul := @quot_of_mul_quot G H dH,
}


/-
Différents lemmes permettant de travailler avec les quotients
-/
lemma mor_quotient_id {G : groupe} {H : sous_groupe G} [dH: est_distingue H]
  : ∀ a : G, mor_quotient H a = ⟦a⟧@H := λ a, rfl
-- ↓ La multiplication sur G/H est compatible avec celle sur G
lemma quot_of_mul_quot' {G : groupe} {H : sous_groupe G} [dH: est_distingue H]
  : ∀ a b : G, ( (⟦a⟧@H * ⟦b⟧@H) : G/*H ) = (⟦a*b⟧@H) := @quot_of_mul_quot G H dH
-- ↓ L'inverse est aussi compatible
lemma quot_of_inv_quot' {G : groupe} {H : sous_groupe G} [dH : est_distingue H]
  : ∀ a : G, ((⟦a⟧@H)⁻¹ : G/*H) = ⟦a⁻¹⟧@H :=
  by{intro, rw [←mor_quotient_id, ← mor_quotient_id, mor_inv_inv_mor]}
-- ↓ le neutre du groupe quotient est la classe du neutre dans G
lemma one_quot_is_class_one {G : groupe} {H : sous_groupe G} [dH: est_distingue H]
  : (1: G/*H) = ⟦1⟧@H := rfl
-- ↓ multiplier par un élément de H ne change pas la classe
lemma class_xh_is_x {G : groupe} {H : sous_groupe G} [dH: est_distingue H]
  (a : G) (h : H) : (⟦a*h⟧@H) = (⟦a⟧@H) :=
begin
  apply quot.sound, apply rel_gauche_symm, 
  existsi h.val, existsi h.property, refl, 
end

-- ↓ Tout élément de la classe de 1 est dans H
lemma repr_quot_one_in {G : groupe} (H : sous_groupe G) [dH: est_distingue H]
  : (repr_quot (1:G/*H)).val ∈ H :=
begin
  have p := (repr_quot (1:G/*H)).property,
  rw one_quot_is_class_one at p ⊢,
  have p₂ := quot_gauche_exact _ _ p,
  cases p₂ with h tmp, cases tmp with h_H ph,
  rw [G.mul_droite_all _ _ h⁻¹, mul_assoc', neutre_gauche', inv_droite, neutre_droite] at ph,
  rw ←ph,
  exact H.inv_stab _ h_H,
end
-- ↓ la classe de 1 est exactement H
lemma class_one_iff {G : groupe} (H : sous_groupe G) [dH: est_distingue H] (a : G)
  : (⟦a⟧@H) = (1:G/*H) ↔ a ∈ H :=
begin
  split; intro p,
  rw one_quot_is_class_one at p, have p₂ := quot_gauche_exact _ _ p,
  cases p₂ with h tmp, cases tmp with h_H ph,
  rw (G.inv_unique ph.symm),
  exact H.inv_stab _ h_H,
  apply quot.sound, existsi a⁻¹, existsi H.inv_stab _ p, rw inv_droite, 
end


-- L'application classe mor_quotient est surjective
lemma mor_quotient_surj {G : groupe} {H : sous_groupe G} [dH : est_distingue H]
  : function.surjective (mor_quotient H) :=
begin
  intro b, existsi (repr_quot b).val,
  exact (repr_quot b).property,
end

/-**************************************FIN Ensemble quotient et groupe quotient **************************************-/




@[instance] lemma preim_distingue_est_distingue {G H : groupe} (f : G  →* H) {K : sous_groupe H}
  (dK : K ⊲ H) : (↩(im_recip f K)) ⊲ G :=
begin
  rw carac_est_distingue at dK ⊢, 
  intros h ph g, rw mem_ss_groupe_simp at ph ⊢,
  rw [sous_groupe_de_est_sous_groupe_id, ←in_ens_image] at ph ⊢,
  repeat {rw mor_resp_mul}, rw mor_inv_inv_mor,
  exact dK _ ph (f g), 
end


@[instance] lemma ker_est_distingue {G H : groupe} (f : G  →* H) : ((↩(ker f)) ⊲ G) :=
begin
  simp only [ker_est_preim_neutre f],
  apply preim_distingue_est_distingue f (triv_est_distingue H), 
end


lemma centre_est_distingue (G : groupe) : (↩(centre G)) ⊲ G :=
begin
  rw carac_est_distingue,
  intros h h_comm g,
  rw [mem_ss_groupe_simp, sous_groupe_de_est_sous_groupe_id] at h_comm ⊢,
  rw ←h_comm g,
  rw [mul_assoc',inv_droite,neutre_droite],
  exact h_comm,
end


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

lemma card_ss_groupe_div_card_groupe {G : groupe} (H : sous_groupe G) [fG : est_fini G]
  : (cardinal H) ∣ (cardinal G) := Exists.intro (cardinal (G/.H)) (theoreme_de_lagrange H)

end groupe