import .generique
import .cardinalite_finie
import base
import morphismes
import sous_groupes
import quotient
import ordre
import distingue


open generique

namespace groupe

lemma mor_quot_ker_inj {G G' : groupe} {f : G  →* G'} (fI : function.injective f)
  : est_isomorphisme  (mor_quotient (↩ker f)) :=
begin
  rw carac_mor_inj at fI,
  rw carac_est_isomorphisme, split, { -- injectif
    intros a b ab, repeat{rw mor_quotient_id at ab},
    have ab' := quot_gauche_exact _ _ ab,
    cases ab' with k hk, cases hk with k_K hk,
    rw [sous_groupe_de_est_sous_groupe_id, fI, in_singleton] at k_K,
    rw [hk, k_K, neutre_droite],
  }, { --surjectif
    exact mor_quotient_surj,
  }
end

lemma iso_quot_ker_inj {G G' : groupe} {f : G  →* G'} (fI : function.injective f)
  : G ≋ G/*↩ker f := by{existsi (mor_quotient _), exact mor_quot_ker_inj fI,}

theorem theoreme_de_factorisation {G G': groupe} (f : G  →* G') (H : sous_groupe G)
  [dH : est_distingue H] (H_ker : ∀ x : H, f x = 1): ∃! f' : morphisme (G/*H) G', f = f' ∘₁ (mor_quotient H) :=
begin
  have f_resp_rel_gauche : ∀ a b : G, rel_gauche_mod H a b → f a = f b,
    intros a b pab,
    cases pab with h tmp, cases tmp with h_H p, 
    rw [G.mul_gauche_all _ _ a⁻¹, ←mul_assoc', inv_gauche',neutre_gauche'] at p,
    apply eq.symm,
    rw [mul_left_inv_eq_one_of_eq, ←mor_inv_inv_mor, ←mor_resp_mul],
    rw p,
    exact H_ker ⟨h, h_H⟩,
  let f' : (G/*H) → G' := (quot.lift f f_resp_rel_gauche),
  have f'_resp_mul : ∀ A B : (G/*H), f' (A*B) = f' A * f' B,
    intro A, apply quot.ind, intro b, revert A, apply quot.ind, intro a,
    repeat {rw ←mor_quotient_id}, rw ← mor_resp_mul, repeat {rw mor_quotient_id},
    have why: ∀ x, f' (⟦x⟧@H) = (quot.lift f f_resp_rel_gauche) (⟦x⟧@H), intro,refl,
    repeat{rw [why, quot_lift_id f dH]},
    exact f.resp_mul a b,
  apply exists_unique.intro (⟨f', f'_resp_mul⟩ : morphisme (G/*H) G'),
  { -- preuve que f = f' ∘ cl 
    rw morphisme_eq_iff, funext, 
    rw comp_mor_id,
    unfold mor_quotient,
  }, { -- preuve de l'unicite
    intros g pg,
    rw morphisme_eq_iff, funext,
    simp [mor_id],
    have p₀ : (⟦repr_quot x⟧@H) = x:= class_of_repr_quot x,
    rw ← p₀,
    conv {to_lhs, rw [←mor_quotient_id, mor_id, ← comp_mor_id, ←pg]},
  }
end


theorem pre_theoreme_isomorphisme₁ {G G' : groupe} (f : G  →* G')
  : ∃! f' : morphisme (G/*(↩ker f)) ↩im f, f = plongeon _ ∘₁ f' ∘₁ (mor_quotient ↩(ker f)) :=
begin
  
  -- On prend la fonction dont l'existence est démontrée par le théorème de factorisation 
  have p₁ := theoreme_de_factorisation (f↓) (↩(ker (f))) 
    (by {intro, apply subtype.eq,rw mor_vu_dans_im_id, exact x.property,}),
  cases p₁ with f' tmp, cases tmp with pf' f'_unique, 
  existsi f',

  split;simp,
  { -- On montre qu'elle satisfait : f = i∘f'∘cl 
    rw morphisme_eq_iff at ⊢ pf', funext,
    rw ←mor_vu_dans_im_id,
    rw pf',
    refl,  
  }, { -- On montre l'unicité
    intros g pg, 
    have p₁ := f'_unique g, 
    rw morphisme_eq_iff at ⊢ pf' pg p₁,
    simp at p₁,
    apply p₁,
    rw morphisme_eq_iff, funext,
    apply subtype.eq,
    rw mor_vu_dans_im_id,
    rw pg,
    refl, 
  }
end


theorem theoreme_isomorphisme₁ {G G' : groupe} (f : G  →* G')
  : (G/*↩ker f) ≋ ↩im f :=
begin
  have p₁ := pre_theoreme_isomorphisme₁ f, 
  cases p₁ with f' tmp, cases tmp with p₁, 
  existsi f', 
  rw carac_est_isomorphisme,
  simp [morphisme_eq_iff₂, comp_mor_fun_eq] at p₁,
  split, { -- Injectif
    rw [carac_mor_inj, ←set_eq], simp only [in_singleton, ←im_one_in_ker],
    apply quot.ind, intro, 
    split;intro p, 
      have p₂ := app_eq (plongeon _) p,
      rw [←mor_quotient_id, ←p₁ a, plongeon_id, coe_sous_groupe, coe_one_sous_groupe] at p₂,
      rw im_one_in_ker at p₂,
      rw class_one_iff,
      exact p₂,
      rw [p, mor_neutre_est_neutre],
  }, { -- Surjectif 
    intro b, cases b.property with a fa_b,
    existsi ⟦a⟧@_,
    rw ←eq_in_ss_groupe_iff_eq, 
    rw [←plongeon_id, ←mor_quotient_id],
    rw [←p₁, fa_b, coe_sous_groupe], 
  }
end

lemma theoreme_isomorphisme₁_inj {G G' : groupe} {f : G  →* G'} (fI : function.injective f)
  : G ≋ ↩im f :=
begin
  have p₀ : G ≋ G/*↩ker f := iso_quot_ker_inj fI, 
  have p₁ : G/*↩ker f ≋ ↩im f := theoreme_isomorphisme₁ _, 
  exact sont_isomorphes_trans p₀ p₁,
end

lemma theoreme_isomorphisme₁_surj {G G' : groupe} {f : G  →* G'} (fS : function.surjective f)
  : G/*↩ker f ≋ G' :=
begin
  have p₀ :  G/*↩ker f ≋ ↩im f := theoreme_isomorphisme₁ _,
  have p₁ : ↩im f ≋ G' := sont_isomorphes_symm.1 (im_surj_isomorphe_arrivee _ fS),
  exact sont_isomorphes_trans p₀ p₁,
end


-- Définitions en rapport avec le théorème d'isomorphisme 2 : 
-- Pour H < G et K ⊲ G, on définit HK < G et on montre que K∩H ⊲ G
def ss_groupe_mul_ss_groupe {G : groupe} (H K : sous_groupe G)
  : set G :=  {x | ∃ (h∈H) (k∈K), x = h*k}
local notation H `*₀`:57 K:57 := ss_groupe_mul_ss_groupe H K
local notation H `⬝`:67 K:67 := (↩H*₀K)

@[instance] lemma ss_mul_distingue_est_sous_groupe {G : groupe} (H K : sous_groupe G)
  [est_distingue K] : est_sous_groupe (H*₀K) :=
begin
  have p₁ : (H*₀K) = im_recip (mor_quotient K) (ens_image (mor_quotient K) H),
    rw ←set_eq, intro, split; intro p, 
      { -- HK ⊆ cl⁻¹(cl(H)) 
        cases p with h tmp, cases tmp with h_H tmp,
        cases tmp with k tmp, cases tmp with k_K phk,   
        rw [←in_ens_image, mor_quotient_id],
        have p' := app_eq (@quot.mk G (G%.K)) phk,
        rw [p', coe_sous_groupe₂ k k_K, class_xh_is_x], 
        existsi [(h:G), h_H], 
        rw mor_quotient_id,
      }, { -- cl⁻¹(cl(H)) ⊆ HK 
        rw [←in_ens_image] at p,
        cases p with h tmp, cases tmp with h_H ph, 
        rw [mor_quotient_id, mor_quotient_id] at ph,
        have p₂ := quot_gauche_exact _ _ ph,
        cases p₂ with k tmp, cases tmp with k_K p,
        existsi [h, h_H, k, k_K], 
        exact p,
      },
  have p₂ := preim_ss_groupe_est_ss_groupe (mor_quotient K) (↩(ens_image (mor_quotient K) H)),
  rw sous_groupe_de_est_sous_groupe_id at p₂,
  rw ←p₁ at p₂,
  exact p₂,
end

@[instance] lemma H_inclus_HK {G : groupe} (H K : sous_groupe G)
  [est_distingue K] : H ⊆₁ (H⬝K) :=
begin
  split, intros h h_H, rw sous_groupe_de_est_sous_groupe_id,
  existsi [h, h_H, (1:G), K.contient_neutre], rw neutre_droite,
end

@[instance] lemma K_inclus_HK {G : groupe} (H K : sous_groupe G)
  [est_distingue K] : K ⊆₁ (H⬝K) :=
begin
  split, intros k k_K, rw sous_groupe_de_est_sous_groupe_id,
  existsi [(1:G), H.contient_neutre, k, k_K], rw neutre_gauche',
end

instance intersection_sous_groupes {G : groupe} : has_inter (sous_groupe G) := ⟨λ H K, ↩((H : set G)∩K)⟩ 

@[instance] lemma KiH_inclus_HK {G : groupe} (H K : sous_groupe G)
  [est_distingue K] : (K ∩ H) ⊆₁ (H⬝K) := by {split, intros a pa, exact (K_inclus_HK _ _).h _ pa.1}

@[instance] lemma KiH_inclus_H {G : groupe} (H K : sous_groupe G)
  [est_distingue K] : (K∩H) ⊆₁ H := by {split, intros g pg, exact pg.2}

-- Le morphisme naturel de H vers HK
def injection_H_HK {G : groupe} (H K : sous_groupe G) [est_distingue K] : morphisme H (H⬝K) :=
{
  mor := λ h, ⟨h.val, (H_inclus_HK _ _).h _ h.property⟩,
  resp_mul := begin
    intros, 
    apply subtype.eq,
    rw [@coe_mul_sous_groupe _ (H⬝K), coe_mul_sous_groupe],
  end
}

-- La suite p : H → HK → HK/K de la preuve du polycopié
def suite_comp_thm_iso₂ {G : groupe} (H K : sous_groupe G) [dK : est_distingue K]
  : morphisme H ((H⬝K) /* K↘(H⬝K))
  := (mor_quotient (K↘(↩H⬝K))) ∘₁ (injection_H_HK _ _)

lemma ker_suite_comp_thm_iso₂ {G : groupe} (H K : sous_groupe G) [dK : est_distingue K]
  : ((K∩H)↘H) = ↩(ker (suite_comp_thm_iso₂ H K)) :=
begin
  rw [sous_groupe_eq_iff, sous_groupe_down_ens, sous_groupe_de_est_sous_groupe_id],
  rw ←set_eq, intro h, split;intro p;
  rw ←im_one_in_ker at *;
  unfold suite_comp_thm_iso₂ at *; 
  rw [comp_mor_fun_eq, function.comp_app, mor_quotient_id, class_one_iff] at *,
    exact p.1,-- K∩H ⊆ ker p (Ex compli)
    exact ⟨p, h.property⟩, --ker p ⊆ K∩H
end

lemma im_suite_comp_thm_iso₂ {G : groupe} (H K : sous_groupe G) [dK : est_distingue K]
  : function.surjective (suite_comp_thm_iso₂ H K) :=
begin
  intro, cases (repr_quot b) with b_v p₁, cases b_v with b_v p₂,
  cases p₂ with h t, cases t with h_H t, cases t with k t, cases t with k_K phk, 
  existsi (⟨h,h_H⟩:H), 
  unfold suite_comp_thm_iso₂,  
  rw [comp_mor_fun_eq, function.comp_app, mor_quotient_id,←p₁],
  apply quot.sound,
  existsi (⟨⟨k, (K_inclus_HK _ _).h _ k_K⟩, k_K⟩: K↘(H⬝K)).val,
  existsi k_K,
  apply subtype.eq,
  exact phk,
end

@[instance] lemma K_inter_H_distingue_H {G : groupe} (H K : sous_groupe G)
  [dK : est_distingue K] : est_distingue ((K∩H)↘H) :=
begin
  have ker_p_distingue := ker_est_distingue (suite_comp_thm_iso₂ H K),
  rw ←ker_suite_comp_thm_iso₂ at ker_p_distingue, 
  exact ker_p_distingue,
end

theorem theoreme_isomorphisme₂ {G : groupe} (H K : sous_groupe G) [dK : est_distingue K]
  : H /* (K∩H)↘H ≋ (H⬝K) /* K↘(H⬝K) :=
begin
  have h₂ :  (↩ im (suite_comp_thm_iso₂ H K)) ≋ (((H⬝K))/*(K↘(H⬝K))),
    rw sont_isomorphes_symm,
    exact im_surj_isomorphe_arrivee (suite_comp_thm_iso₂ H K) (im_suite_comp_thm_iso₂ H K),
  have h₁ : H /* (K∩H)↘H ≋ ↩im (suite_comp_thm_iso₂ H K),
    simp only [ker_suite_comp_thm_iso₂ H K], 
    exact theoreme_isomorphisme₁ (suite_comp_thm_iso₂ H K),
  exact sont_isomorphes_trans h₁ h₂,
end

-- Classe permettant de plonger un groupe dans un autre en fournissant une injection canonique.
-- Cette classe est utile pour le troisième théorème d'isomorphisme: on voit dans celui-ci le 
-- quotient (G/K)/(H/K): 
--   -Dans le formalisme ZFC, cela ne pose pas de problème: on peut montrer 
--    que l'ensemble H/K des classes est bien un sous ensemble de l'ensemble G/K des classes,
--    et que leurs lois de multiplication respectives sont les mêmes, et que H/K ⊲ G/K
--   -Dans le formaliste de Lean, en définissant les quotients avec quot.mk, G/K et H/K sont deux
--    objets complétement distincts, et il faut alors indiquer à lean que H/K est considéré comme
--    un sous groupe de G/K avec l'injection naturelle : λ ⟦h:H⟧@K, ⟦h:G⟧@K
class injection_naturelle (G G': groupe) :=
  (mor : G  →* G')
  (mor_inj : function.injective mor)

-- Si G' injecte G par une injection i, le sous groupe représentant G' dans G est i
@[reducible] def sous_groupe_de_injection_naturelle  (G G' : groupe) [GiG' : injection_naturelle G G']
  : sous_groupe G' := (↩im GiG'.mor)

local notation G `↪`:60 G':60 := sous_groupe_de_injection_naturelle G G' 

lemma bijection_de_injection_naturelle (G G' : groupe) [i : injection_naturelle G G']
  : G ≋ G↪G' :=
begin
  have p₀ : G ≋ ↩im i.mor := theoreme_isomorphisme₁_inj i.mor_inj,
  unfold sous_groupe_de_injection_naturelle, 
  exact p₀, 
end

lemma sous_groupe_de_injection_naturelle_id (G G' : groupe) [i : injection_naturelle G G']
  : (G↪G') = ↩im i.mor := rfl 

-- Une reformulation du fait que H/K (vu comme un ensemble de classes) est inclus dans G/K
lemma double_quot_sub_quot {G : groupe} (H K : sous_groupe G) [HinK : K ⊆₁ H]
  {a b : H} (a_equiv_b : ⟦a⟧@(K↘H) = ⟦b⟧@(K↘H)) : ⟦a⟧@K = ⟦b⟧@K :=
begin
  have aeb := quot_gauche_exact _ _ a_equiv_b,
  cases aeb with k t, cases t with k_K pab,
  rw pab, 
  apply quot.sound,
  existsi [k.val, k_K],
  refl,
end

noncomputable def plongeon_HdK_GdK {G : groupe} {H K : sous_groupe G} [KinH : K ⊆₁ H] [dK : K⊲G]
  : morphisme (H/*(K↘H)) (G/*K) := 
{
  mor := λ a, ⟦(repr_quot a).val.val⟧@K,
  resp_mul := begin
    intros a b,
    rw quot_of_mul_quot', 
    rw ←coe_mul_sous_groupe,
    repeat{rw ←coe_sous_groupe},
    apply double_quot_sub_quot H K,
    rw (repr_quot ((a*b):H/*(K↘H))).property,
    rw ←quot_of_mul_quot',
    rw [(repr_quot a).property,(repr_quot b).property],
  end
}


lemma plongeon_HdK_GdK_id {G : groupe} (H K : sous_groupe G) [KinH : K ⊆₁ H] [dK : K⊲G]
  : ∀ a : H/*(K↘H), (plongeon_HdK_GdK a) = (⟦(repr_quot a).val.val⟧@K) := λa, rfl
lemma plongeon_HdK_GdK_id₂ {G : groupe} (H K : sous_groupe G) [KinH : K ⊆₁ H] [dK : K⊲G]
  : ∀ h : H, (plongeon_HdK_GdK ⟦h⟧@(K↘H)) = ⟦h.val⟧@K :=
begin
  intro, rw plongeon_HdK_GdK_id, apply quot.sound,
  have p₀ := (repr_quot ⟦h⟧@(K↘H)).property,
  have p₁ := quot_gauche_exact _ _ p₀,
  cases p₁ with k t, cases t with k_K pk,
  existsi k.val, existsi k_K, 
  rw ←coe_mul_sous_groupe,
  conv{to_lhs,rw pk},
end

lemma plongeon_HdK_GdK_im_distingue {G : groupe} (H K : sous_groupe G) [KinH : K ⊆₁ H] [dK : K⊲G] [dH : H⊲G]
  : est_distingue ↩im (@plongeon_HdK_GdK _ H K _ _) :=
begin
  rw carac_est_distingue, intros B ha,
  cases ha with A pA,
  rw ←(repr_quot A).property at pA,
  rw plongeon_HdK_GdK_id₂ at pA,
  apply quot.ind,
  intro g,
  rw [←pA, quot_of_mul_quot', quot_of_inv_quot',quot_of_mul_quot'],
  let ghg : H := ⟨g*(repr_quot A).val.val*g⁻¹, (carac_est_distingue H).1 dH _ (repr_quot A).val.property g⟩,
  have p₁ : ghg.val = g * (repr_quot A).val.val * g⁻¹ := rfl,
  rw ←p₁,
  rw ←plongeon_HdK_GdK_id₂,
  exact im_point_in_im _ _,
end

@[instance] noncomputable def injection_naturelle_HdK_GdK {G : groupe} (H K : sous_groupe G) [KinH : K ⊆₁ H] [dK : K⊲G]
  : injection_naturelle (H/*(K↘H)) (G/*K) := 
{
  mor := plongeon_HdK_GdK, -- On définit le morphisme naturel H/K → G/K 
  mor_inj := begin
    intros a b pab, 
    rw [←(repr_quot a).property, ←(repr_quot b).property],
    have p₀ := quot_gauche_exact _ _ pab,
    cases p₀ with k t, cases t with k_K p₀,
    apply quot.sound,
    existsi (⟨k, KinH.h _ k_K⟩:H), existsi k_K,
    apply subtype.eq,
    exact p₀,
  end
}

@[instance] lemma HdK_distingue_dans_GdK {G : groupe} (H K : sous_groupe G) [KinH : K ⊆₁ H] [dK : K⊲G] [dH : H⊲G]
  : ((H/*(K↘H)) ↪ (G/*K)) ⊲ (G/*K) := plongeon_HdK_GdK_im_distingue H K



theorem theoreme_isomorphisme₃ {G : groupe} (H K : sous_groupe G) [dH : H⊲G] [dK : K⊲G] [KinH : K ⊆₁ H] 
  : G/*H ≋ (G/*K) /* (H/*(K↘H) ↪ (G/*K)) :=
begin
  -- Preuve du polycopié : 
    -- On définit la composée naturelle f : G → G/K → (G/K)/(H/K)
    -- Elle est surjective comme composée des fonctions de classe qui sont surjectives
    -- On montre que son noyeau est égal à H
    -- On applique le premier théorème d'isomorphisme à f 
  let f := (mor_quotient (H/*(K↘H) ↪ (G/*K))) ∘₁ (mor_quotient K), 
  have f_surj : function.surjective f := function.surjective.comp mor_quotient_surj mor_quotient_surj,
  have ker_f_eq_H : ↩ker f = H,
    rw [sous_groupe_eq_iff, sous_groupe_de_est_sous_groupe_id, ←set_eq],
    intro a, have p₂ : f a = ⟦⟦a⟧@K⟧@((H/*(K↘H) ↪ G/*K)) := rfl,
    rw [←im_one_in_ker,p₂, class_one_iff],
    have p₃ : (H/*(K↘H) ↪ (G/*K)) = ↩im plongeon_HdK_GdK := rfl,
    split;intro pa; rw p₃ at *, {
      cases pa with A pA,
      rw [plongeon_HdK_GdK_id] at pA,
      have pA' := quot_gauche_exact _ _ pA,
      cases pA' with k t, cases t with k_K pk,
      rw pk,
      exact H.mul_stab _ (repr_quot A).val.property _ (KinH.h _ k_K),
    }, {
      existsi ⟦⟨a, pa⟩⟧@(K↘H),
      rw plongeon_HdK_GdK_id₂, 
    },
  have p₀ : G/*↩ker f ≋ (G/*K) /* (H/*(K↘H) ↪ (G/*K)) := theoreme_isomorphisme₁_surj f_surj, 
  simp only [ker_f_eq_H] at p₀,
  exact p₀,
end

end groupe
