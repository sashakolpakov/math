import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ConstantConormalNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.DifferenceOpenFrames
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.AffineDiagonal

/-! # Infinitesimal Translation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation

noncomputable section

/-! Original identity tangents define actual infinitesimal group
translations. On each original affine chart, this is exactly the
translated lift whose unit coefficients were computed algebraically. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver LieRanks.dualNumberTest

instance dualProductProjection_affine (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    IsAffineHom (snd (LieRanks.dualNumberTest ℂ) X).left := by
  let : MorphismProperty.IsStableUnderBaseChange (@IsAffineHom : MorphismProperty Scheme.{0}) :=
    isAffineHom_isStableUnderBaseChange
  let : IsAffineHom (LieRanks.dualNumberTest ℂ).hom := by
    change IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))))
    infer_instance
  change IsAffineHom (pullback.snd (LieRanks.dualNumberTest ℂ).hom X.hom)
  exact MorphismProperty.of_isPullback (P := @IsAffineHom.{0})
    (IsPullback.of_hasPullback (LieRanks.dualNumberTest ℂ).hom X.hom)
      ‹IsAffineHom (LieRanks.dualNumberTest ℂ).hom›

variable (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) [GrpObj G]

def dualInfinitesimalTranslation (t : DualOpen.Lifts.DualSchemePoints G 1) : LieRanks.dualNumberTest ℂ ⊗ G ⟶ G :=
  (fst (LieRanks.dualNumberTest ℂ) G ≫ t.val) * snd (LieRanks.dualNumberTest ℂ) G

theorem dualInfinitesimalTranslation_reduction (t : DualOpen.Lifts.DualSchemePoints G 1) :
    RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction G ≫ dualInfinitesimalTranslation G t = 𝟙 G := by
  simp only [dualInfinitesimalTranslation, MonObj.comp_mul, RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction,
    lift_fst_assoc, lift_snd, Category.assoc, t.property, MonObj.comp_one, one_mul]

theorem dualInfinitesimalTranslation_equal_reduction (t : DualOpen.Lifts.DualSchemePoints G 1) :
    (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction G).left ≫ (dualInfinitesimalTranslation G t).left =
      (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction G).left ≫ (snd (LieRanks.dualNumberTest ℂ) G).left :=
  congrArg Over.Hom.left ((dualInfinitesimalTranslation_reduction G t).trans
    (Dual.ReductionOpens.dualBaseChangeReduction_projection G).symm)

def dualTranslationLineKernel (L : HilbertConstruction.Line.Bundles.LineBundle G.left) (t : DualOpen.Lifts.DualSchemePoints G 1) : DualLine.ClassKernel.dualLineClassKernel G :=
  DualLine.PullbackDifference.dualLinePullbackDifferenceKernel G (dualInfinitesimalTranslation G t).left
    (snd (LieRanks.dualNumberTest ℂ) G).left (dualInfinitesimalTranslation_equal_reduction G t) L

def dualAffineTranslationChart (B : CommAlgCat ℂ) (i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G) :
    EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber B) ⟶ LieRanks.dualNumberTest ℂ ⊗ G :=
  lift (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber ℂ) (DualNumber B) (Dual.NumberCoefficients.dualNumberAlgMap (Algebra.ofId ℂ B)))
    (Affine.IntrinsicCoefficientPoint.openAffineLiftReference ℂ B G (Affine.ChartCoefficientConormal.affineChartCoefficientPoint ℂ B B G i))

omit [GrpObj G] in
theorem dualAffineTranslationChart_projection (B : CommAlgCat ℂ) (i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G) :
    dualAffineTranslationChart G B i ≫ snd (LieRanks.dualNumberTest ℂ) G =
      Affine.IntrinsicCoefficientPoint.openAffineLiftReference ℂ B G (Affine.ChartCoefficientConormal.affineChartCoefficientPoint ℂ B B G i) :=
  lift_snd _ _

variable [IsIntegral G.left] [Smooth G.hom]

theorem dualAffineTranslationChart_native (B : CommAlgCat ℂ) (i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G)
    (v : Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension G.hom) → ℂ) :
    dualAffineTranslationChart G B i ≫ dualInfinitesimalTranslation G (SchemeDualTangent.nativeSchemeTangentDualEquiv G 1 v) =
      (Affine.ConstantConormalLift.affineConstantConormalLift G B i (IdentityConormalLinear.nativeIdentityConormalLinear G v)).val := by
  rw [Affine.ConstantConormalLift.affineConstantConormalLift_native]
  simp only [dualInfinitesimalTranslation, MonObj.comp_mul, dualAffineTranslationChart, lift_fst_assoc, lift_snd]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation
