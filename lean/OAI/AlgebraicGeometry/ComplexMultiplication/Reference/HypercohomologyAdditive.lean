import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.HypercohomologyPullback

/-! # Hypercohomology Additive -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.HypercohomologyAdditive

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

/-! # Additivity of the genuine original hypercohomology pullback

Exact inverse image is additive on the actual derived categories, so its map
on the original constant-integer localized morphisms is an additive map.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry ComplexPoint Localization

variable {X Y : Over (Spec (.of ℂ))}

local instance originalAnalyticDerivedCategory (Z : Over (Spec (.of ℂ))) :
    HasDerivedCategory (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Z) :=
  HasDerivedCategory.standard _

local instance inverseImageComplex_commShift (f : X ⟶ Y) :
    (AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.CommShift ℤ :=
  inferInstanceAs
    (((AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).CommShift ℤ)

local instance inverseImageDerived_additive (f : X ⟶ Y) :
    (AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapDerivedCategory.Additive := by
  apply (Localization.functor_additive_iff DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y) (ComplexShape.up ℤ))
    (AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapDerivedCategory).2
  exact Functor.additive_of_iso
    (AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapDerivedCategoryFactorsh.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Derived-category expression of the actual original inverse-image map. -/
theorem originalHypercohomologyPullback_equiv (f : X ⟶ Y)
    (K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y) ℤ) (n : ℤ)
    (G : DerivedCategory (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y) ⥤
      DerivedCategory (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)) [G.CommShift ℤ]
    (e : (AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ G) [NatTrans.CommShift e.hom ℤ]
    (γ : ℍ^n(Y; K)) :
    (SmallShiftedHom.equiv (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q)
      (HypercohomologyPullback.originalHypercohomologyPullback f K n γ) =
    (ShiftedHom.mk₀ 0 rfl
      (DerivedCategory.Q.map (AnalyticInverseImage.originalIntegerComplexInverseImageIso f).inv ≫
        e.hom.app (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt Y))).comp
      (((SmallShiftedHom.equiv (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms Y) DerivedCategory.Q γ).map G).comp
        (ShiftedHom.mk₀ 0 rfl (e.inv.app K ≫ DerivedCategory.Q.map
          (𝟙 ((AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.obj K))))
        (zero_add n)) (add_zero n) := by
  exact LocalizerMorphism.equiv_smallShiftedHomMap (AnalyticInverseImage.originalAnalyticInverseImageLocalizer f)
    DerivedCategory.Q DerivedCategory.Q (AnalyticInverseImage.originalIntegerComplexInverseImageIso f)
    (Iso.refl ((AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.obj K)) G e γ

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Additive derived mapping remains additive after fixed pre- and postcomposition. -/
theorem originalDerivedMapSandwich_add
    (G : DerivedCategory (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y) ⥤
      DerivedCategory (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)) [G.CommShift ℤ] [G.Additive]
    {S₁ T₁ : DerivedCategory (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y)}
    {S₂ T₂ : DerivedCategory (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)}
    (A : ShiftedHom S₂ (G.obj S₁) (0 : ℤ))
    (B : ShiftedHom (G.obj T₁) T₂ (0 : ℤ)) (n : ℤ)
    (γ δ : ShiftedHom S₁ T₁ n) :
    A.comp (((γ + δ).map G).comp B (zero_add n)) (add_zero n) =
      A.comp ((γ.map G).comp B (zero_add n)) (add_zero n) +
      A.comp ((δ.map G).comp B (zero_add n)) (add_zero n) := by
  rw [ShiftedHom.map_add, ShiftedHom.add_comp, ShiftedHom.comp_add]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Additivity follows from an additive derived functor representing actual inverse image. -/
theorem originalHypercohomologyPullback_add_of_derived (f : X ⟶ Y)
    (K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y) ℤ) (n : ℤ)
    (G : DerivedCategory (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y) ⥤
      DerivedCategory (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)) [G.CommShift ℤ] [G.Additive]
    (e : (AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ G) [NatTrans.CommShift e.hom ℤ]
    (α β : ℍ^n(Y; K)) :
    HypercohomologyPullback.originalHypercohomologyPullback f K n (α + β) =
      HypercohomologyPullback.originalHypercohomologyPullback f K n α + HypercohomologyPullback.originalHypercohomologyPullback f K n β := by
  apply (SmallShiftedHom.equiv (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
  let T : ShiftedHom (DerivedCategory.Q.obj (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt Y))
      (DerivedCategory.Q.obj K) n →
      ShiftedHom (DerivedCategory.Q.obj (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj ((AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.obj K)) n :=
    fun γ => (ShiftedHom.mk₀ 0 rfl
      (DerivedCategory.Q.map (AnalyticInverseImage.originalIntegerComplexInverseImageIso f).inv ≫
        e.hom.app (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt Y))).comp
      ((γ.map G).comp (ShiftedHom.mk₀ 0 rfl (e.inv.app K ≫ DerivedCategory.Q.map
        (𝟙 ((AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.obj K)))) (zero_add n))
      (add_zero n)
  have hmap (γ : ℍ^n(Y; K)) :
      (SmallShiftedHom.equiv (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q)
        (HypercohomologyPullback.originalHypercohomologyPullback f K n γ) =
      T ((SmallShiftedHom.equiv (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms Y) DerivedCategory.Q) γ) :=
    originalHypercohomologyPullback_equiv f K n G e γ
  have hT (γ δ : ShiftedHom (DerivedCategory.Q.obj (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt Y))
      (DerivedCategory.Q.obj K) n) : T (γ + δ) = T γ + T δ := by
    exact originalDerivedMapSandwich_add G _ _ n γ δ
  rw [ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyEquiv_add]
  exact (hmap (α + β)).trans
    ((congrArg T (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyEquiv_add Y K n α β)).trans
      ((hT _ _).trans (congrArg₂ (· + ·) (hmap α).symm (hmap β).symm)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original inverse-image map is additive on the original hypercohomology groups. -/
theorem originalHypercohomologyPullback_add (f : X ⟶ Y)
    (K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y) ℤ) (n : ℤ) (α β : ℍ^n(Y; K)) :
    HypercohomologyPullback.originalHypercohomologyPullback f K n (α + β) =
      HypercohomologyPullback.originalHypercohomologyPullback f K n α + HypercohomologyPullback.originalHypercohomologyPullback f K n β := by
  let G := (AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapDerivedCategory
  let : G.CommShift ℤ := inferInstanceAs
    ((AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapDerivedCategory.CommShift ℤ)
  let e : (AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ G :=
    (AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapDerivedCategoryFactors.symm
  let : NatTrans.CommShift e.hom ℤ := inferInstanceAs
    (NatTrans.CommShift (AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapDerivedCategoryFactors.inv ℤ)
  exact originalHypercohomologyPullback_add_of_derived f K n G e α β

/-- Bundled additive inverse-image pullback on the original hypercohomology. -/
def originalHypercohomologyPullbackAddHom (f : X ⟶ Y)
    (K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y) ℤ) (n : ℤ) :
    ℍ^n(Y; K) →+ ℍ^n(X; (AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.obj K) :=
  AddMonoidHom.mk' (HypercohomologyPullback.originalHypercohomologyPullback f K n)
    (originalHypercohomologyPullback_add f K n)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.HypercohomologyAdditive
