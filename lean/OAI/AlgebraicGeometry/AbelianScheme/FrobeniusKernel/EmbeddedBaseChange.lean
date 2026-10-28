import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BaseChange

/-! # Embedded Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EmbeddedBaseChange.Construction

noncomputable section

section

/-! Exact comparison of embedded objects through their points on every
test object, together with the native pullback image formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_samePointImageIso {C : Type*} [Category C] {H J G : C}
    (i : H ⟶ G) (j : J ⟶ G) [Mono i] [Mono j]
    (h : ∀ (T : C) (a : T ⟶ G), (∃ x : T ⟶ H, x ≫ i = a) ↔ ∃ y : T ⟶ J, y ≫ j = a) :
    ∃ e : H ≅ J, e.hom ≫ j = i := by
  obtain ⟨f, hf⟩ := (h H i).mp ⟨𝟙 H, Category.id_comp i⟩
  obtain ⟨g, hg⟩ := (h J j).mpr ⟨𝟙 J, Category.id_comp j⟩
  have hfg : f ≫ g = 𝟙 H := by
    apply (cancel_mono i).mp
    exact (Category.assoc f g i).trans
      ((congrArg (fun z => f ≫ z) hg).trans (hf.trans (Category.id_comp i).symm))
  have hgf : g ≫ f = 𝟙 J := by
    apply (cancel_mono j).mp
    exact (Category.assoc g f j).trans
      ((congrArg (fun z => g ≫ z) hf).trans (hg.trans (Category.id_comp j).symm))
  exact ⟨⟨f, g, hfg, hgf⟩, hf⟩

theorem pointImage_postcomp_iso {C : Type*} [Category C] {H G G' T : C}
    (i : H ⟶ G) (e : G ≅ G') (a : T ⟶ G') :
    (∃ x : T ⟶ H, x ≫ (i ≫ e.hom) = a) ↔ ∃ x : T ⟶ H, x ≫ i = a ≫ e.inv := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, e.eq_comp_inv.mpr ((Category.assoc x i e.hom).trans hx)⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (Category.assoc x i e.hom).symm.trans (e.eq_comp_inv.mp hx)⟩

theorem pointImage_baseChange {S S' : Scheme} (s : S' ⟶ S) {H G : Over S}
    (i : H ⟶ G) (T : Over S') (a : T ⟶ (Over.pullback s).obj G) :
    (∃ x : T ⟶ (Over.pullback s).obj H, x ≫ (Over.pullback s).map i = a) ↔
      ∃ x : (Over.map s).obj T ⟶ H,
        x ≫ i = ((Over.mapPullbackAdj s).homEquiv T G).symm a := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨((Over.mapPullbackAdj s).homEquiv T H).symm x, ?_⟩
    exact ((Over.mapPullbackAdj s).homEquiv_naturality_right_symm x i).symm.trans
      (congrArg ((Over.mapPullbackAdj s).homEquiv T G).symm hx)
  · rintro ⟨x, hx⟩
    refine ⟨(Over.mapPullbackAdj s).homEquiv T H x, ?_⟩
    exact ((Over.mapPullbackAdj s).homEquiv_naturality_right x i).symm.trans
      ((congrArg ((Over.mapPullbackAdj s).homEquiv T G) hx).trans
        (((Over.mapPullbackAdj s).homEquiv T G).apply_symm_apply a))

end

/-! Equality of independently specified kernel predicates on all tests
constructs the actual embedded pullback isomorphism of their representatives. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S S' : Scheme} (s : S' ⟶ S)
variable {H G : Over S} {J G' : Over S'}
variable (i : H ⟶ G) (j : J ⟶ G') (e : (Over.pullback s).obj G ≅ G')
variable (P : ∀ (T : Over S), (T ⟶ G) → Prop)
variable (P' : ∀ (T : Over S'), (T ⟶ G') → Prop)
variable (hP : ∀ (T : Over S) (a : T ⟶ G), (∃ h : T ⟶ H, h ≫ i = a) ↔ P T a)
variable (hP' : ∀ (T : Over S') (a : T ⟶ G'), (∃ h : T ⟶ J, h ≫ j = a) ↔ P' T a)
variable (htransport : ∀ (T : Over S') (a : T ⟶ (Over.pullback s).obj G),
  P' T (a ≫ e.hom) ↔ P ((Over.map s).obj T) (((Over.mapPullbackAdj s).homEquiv T G).symm a))

include hP hP' htransport in
theorem embeddedKernelPointImage_baseChange (T : Over S') (a : T ⟶ G') :
    (∃ h : T ⟶ (Over.pullback s).obj H, h ≫ ((Over.pullback s).map i ≫ e.hom) = a) ↔
      ∃ h : T ⟶ J, h ≫ j = a := by
  have ht := htransport T (a ≫ e.inv)
  have ha : (a ≫ e.inv) ≫ e.hom = a := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [ha] at ht
  exact (pointImage_postcomp_iso ((Over.pullback s).map i) e a).trans
    ((pointImage_baseChange s i T (a ≫ e.inv)).trans
      ((hP ((Over.map s).obj T) _).trans (ht.symm.trans (hP' T a).symm)))

include hP hP' htransport in
theorem exists_embeddedKernelBaseChangeIso [Mono i] [Mono j] :
    ∃ eH : (Over.pullback s).obj H ≅ J,
      eH.hom ≫ j = (Over.pullback s).map i ≫ e.hom := by
  have : Mono ((Over.pullback s).map i) := inferInstance
  have : Mono ((Over.pullback s).map i ≫ e.hom) :=
    mono_comp' (inferInstanceAs (Mono ((Over.pullback s).map i))) (inferInstanceAs (Mono e.hom))
  exact exists_samePointImageIso _ _ (embeddedKernelPointImage_baseChange s i j e P P' hP hP' htransport)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EmbeddedBaseChange.Construction
