import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCoverCoefficients
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.OrderedForget
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CoefficientComposition

/-! # Top Cover Coefficient Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCoverCoefficientCoordinates

noncomputable section

/-! The additive forgetful source coordinate followed by its actual
double lift equals the original native top-cover coefficient input. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem mapped_composite {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B E : C} {T : D}
    (a : A ⟶ B) (b : B ⟶ E) (c : F.obj E ⟶ T) :
    F.map (a ≫ b) ≫ c = F.map a ≫ F.map b ≫ c := by
  rw [Functor.map_comp, Category.assoc]

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (g : ℕ) [SmoothOfRelativeDimension g X.hom]
  {ι : Type} [LinearOrder ι] (U : ι → X.left.Opens)

open OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCoverCoefficients
abbrev lift := AdditiveTop.Comparison.lift
abbrev forget := forget₂ (ModuleCat (Truncated.Witt.Ring p k n)) AddCommGrpCat
abbrev additiveIso := Ordered.SingleGlobalSourceCoefficients.coefficientIso
  lift (TopCoverCoefficients.form p k n X g).presheaf U g

omit [Fintype k] [CharP k p] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [SmoothOfRelativeDimension g X.hom] in
theorem comparison :
    lift.map ((ModuleCech.CohomologyNaturality.forgetHomologyIso
      (Truncated.Witt.Ring p k n) X U (TopCoverCoefficients.form p k n X g) g).hom ≫
      homologyMap (OrderedCech.Projection.map U (TopCoverCoefficients.form p k n X g).presheaf) g) ≫
      (additiveIso p k n X g U).hom = TopCoverCoefficients.inputMap p k n X g U := by
  let : PreservesColimitsOfSize.{2,2} (TopCoverCoefficients.second p k) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{2,1,2,2}
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
  have hp := ModuleCech.OrderedForget.comparison (Truncated.Witt.Ring p k n)
    X (TopCoverCoefficients.form p k n X g) U g
  have h₀ := OrderedCech.CoefficientComposition.homology U
    (forget p k n) lift (TopCoverCoefficients.module p k n X g) g
  have h₁ := OrderedCech.CoefficientComposition.homology.{0,1,0,3,2,3,2}
    (A := ModuleCat.{0} (Truncated.Witt.Ring p k n))
    (B := ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)))
    (D := AddCommGrpCat.{2}) U
    (TopCoverCoefficients.first p k n) (TopCoverCoefficients.second p k) (TopCoverCoefficients.module p k n X g) g
  have hc :
      lift.map (Ordered.SingleGlobalSourceCoefficients.coefficientIso
        (forget p k n) (TopCoverCoefficients.module p k n X g) U g).hom ≫
        (additiveIso p k n X g U).hom =
      (TopCoverCoefficients.second p k).map (TopCoverCoefficients.firstIso p k n X g U).hom ≫ (TopCoverCoefficients.secondIso p k n X g U).hom :=
    h₀.trans h₁.symm
  have he := congrArg (fun t => lift.map t ≫ (additiveIso p k n X g U).hom) hp.symm
  refine he.trans ?_
  exact (mapped_composite lift _ _ _).trans
    ((congrArg (fun t => lift.map ((forget p k n).map
      (Module.OrderedCoverCoordinates.projection (Truncated.Witt.Ring p k n)
        X (TopCoverCoefficients.form p k n X g) U g)) ≫ t) hc).trans
      (mapped_composite (TopCoverCoefficients.second p k)
        ((TopCoverCoefficients.first p k n).map (Module.OrderedCoverCoordinates.projection
          (Truncated.Witt.Ring p k n) X (TopCoverCoefficients.form p k n X g) U g))
        (TopCoverCoefficients.firstIso p k n X g U).hom (TopCoverCoefficients.secondIso p k n X g U).hom).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCoverCoefficientCoordinates
