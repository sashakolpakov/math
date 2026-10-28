import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularInverseImage
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularConstantSheafNaturality
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ConstantDeRhamNaturality

/-! # Singular Constant Naturality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularConstantNaturality

noncomputable section

/-! # Original constant-to-singular comparison under genuine inverse image

The original constant inclusion commutes with the actual singular pullback,
both on the unchanged complexes and on their original hypercohomology.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry ComplexPoint
open OAI.AlgebraicTopology.Singular

variable {X Y : Over (Spec (.of ℂ))} (R : Type) [CommRing R]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual original constant inclusion is natural in nonnegative singular complexes. -/
theorem originalSingularInverseImagePullbackNat_constants (f : X ⟶ Y) :
    ((AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainSheafComplex R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) ≫
      SingularInverseImage.originalSingularInverseImagePullbackNat R f =
    (ConstantNaturality.originalConstantComplexInverseImageIsoNat f (AddCommGrpCat.of R)).hom ≫
      AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainSheafComplex R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) := by
  ext i
  cases i with
  | zero =>
    change (AnalyticInverseImage.originalAnalyticSheafInverseImage f).map
        (AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZeroSheaf R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) ≫
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
        (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).homEquiv _ _).symm
          (AlgebraicTopology.Singular.SheafCochainRestriction.singularRestrictionSheaf R (DeRhamPresheafPullback.originalAnalyticSchemeMap f) 0) =
      (ConstantNaturality.originalConstantComplexInverseImageIsoNat f (AddCommGrpCat.of R)).hom.f 0 ≫
        AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZeroSheaf R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
    rw [ConstantNaturality.originalConstantComplexInverseImageIsoNat_hom_zero]
    let g₀ : (TopCat.Sheaf.pullback AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).obj
        (AlgebraicTopology.Singular.SheafCochain.singularCochainSheaf R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)) 0) ⟶
      AlgebraicTopology.Singular.SheafCochain.singularCochainSheaf R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) 0 :=
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
        (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).homEquiv _ _).symm
          (AlgebraicTopology.Singular.SheafCochainRestriction.singularRestrictionSheaf R (DeRhamPresheafPullback.originalAnalyticSchemeMap f) 0)
    let e₀ : (TopCat.Sheaf.pullback AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).obj
        ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))).obj
          (AddCommGrpCat.of R)) ⟶
      (AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).obj (AddCommGrpCat.of R) :=
      (AnalyticInverseImage.originalAnalyticConstantInverseImageIso f).hom.app (AddCommGrpCat.of R)
    change (TopCat.Sheaf.pullback AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).map
        (AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZeroSheaf R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) ≫ g₀ =
      e₀ ≫ AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZeroSheaf R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
    apply ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
      (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    have hg₀ : (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
        (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).homEquiv _ _ g₀ =
      AlgebraicTopology.Singular.SheafCochainRestriction.singularRestrictionSheaf R (DeRhamPresheafPullback.originalAnalyticSchemeMap f) 0 := Equiv.apply_symm_apply _ _
    have he₀ : (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
        (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).homEquiv _ _ e₀ =
      ConstantPullback.originalConstantSheafPullback f (AddCommGrpCat.of R) :=
      ConstantInverseImageNaturality.originalAnalyticConstantInverseImageIso_homEquiv f (AddCommGrpCat.of R)
    rw [hg₀, he₀]
    exact SingularConstantSheafNaturality.originalSingularRestrictionSheaf_constants R f
  | succ i =>
    exact ((AnalyticInverseImage.originalAnalyticSheafInverseImage f).map_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 _ (i + 1)
        (Nat.succ_ne_zero i))).eq_of_src _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual original constant inclusion is natural in every integer singular degree. -/
theorem originalSingularInverseImagePullback_constants (f : X ⟶ Y) :
    (AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.map
        (ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt Y R) ≫ SingularInverseImage.originalSingularInverseImagePullback R f =
      (ConstantDeRhamNaturality.originalCoefficientComplexInverseImageIso f (AddCommGrpCat.of R)).hom ≫
        ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X R := by
  unfold SingularInverseImage.originalSingularInverseImagePullback ConstantDeRhamNaturality.originalCoefficientComplexInverseImageIso
    ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt
  change (((AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap
        (AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainSheafComplex R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
          ComplexShape.embeddingUpNat) ≫
      (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (AnalyticInverseImage.originalAnalyticSheafInverseImage f)
        (AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
          ComplexShape.embeddingUpNat).hom) ≫
        HomologicalComplex.extendMap (SingularInverseImage.originalSingularInverseImagePullbackNat R f)
          ComplexShape.embeddingUpNat = _
  rw [Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso_naturality, Category.assoc,
    ← HomologicalComplex.extendMap_comp, originalSingularInverseImagePullbackNat_constants]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    HomologicalComplex.extendMap_comp]
  rfl

/-- Actual pullback of original constant-coefficient hypercohomology. -/
def originalCoefficientConstantHypercohomologyPullback (f : X ⟶ Y) (n : ℤ) :
    ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology Y (ComplexPoint.Basic.ComplexSchemePoint.constantCoefficientSheafComplexInt Y R) n →
      ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.constantCoefficientSheafComplexInt X R) n := fun α ↦
  ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ConstantDeRhamNaturality.originalCoefficientComplexInverseImageIso f (AddCommGrpCat.of R)).hom n
    (HypercohomologyPullback.originalHypercohomologyPullback f (ComplexPoint.Basic.ComplexSchemePoint.constantCoefficientSheafComplexInt Y R) n α)

/-- Actual pullback of the original singular-resolution hypercohomology. -/
def originalSingularHypercohomologyPullback (f : X ⟶ Y) (n : ℤ) :
    ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology Y (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt Y R) n →
      ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X R) n := fun α ↦
  ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (SingularInverseImage.originalSingularInverseImagePullback R f) n
    (HypercohomologyPullback.originalHypercohomologyPullback f (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt Y R) n α)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The unchanged constant-to-singular comparison commutes with actual hypercohomology pullback. -/
theorem originalSingularHypercohomologyPullback_constantComparison (f : X ⟶ Y) (n : ℤ)
    (α : ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology Y (ComplexPoint.Basic.ComplexSchemePoint.constantCoefficientSheafComplexInt Y R) n) :
    originalSingularHypercohomologyPullback R f n
        (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap Y (ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt Y R) n α) =
      ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X R) n
        (originalCoefficientConstantHypercohomologyPullback R f n α) := by
  unfold originalSingularHypercohomologyPullback originalCoefficientConstantHypercohomologyPullback
  let β := HypercohomologyPullback.originalHypercohomologyPullback f (ComplexPoint.Basic.ComplexSchemePoint.constantCoefficientSheafComplexInt Y R) n α
  have hn := HypercohomologyPullback.originalHypercohomologyPullback_naturality f
    (ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt Y R) n α
  have hc := originalSingularInverseImagePullback_constants R f
  exact (congrArg (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (SingularInverseImage.originalSingularInverseImagePullback R f) n) hn).trans
    ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply X
      ((AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.map
        (ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt Y R))
      (SingularInverseImage.originalSingularInverseImagePullback R f) n β).symm.trans
        ((congrArg (fun g ↦ ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X g n β) hc).trans
          (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply X
            (ConstantDeRhamNaturality.originalCoefficientComplexInverseImageIso f (AddCommGrpCat.of R)).hom
            (ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X R) n β)))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularConstantNaturality
