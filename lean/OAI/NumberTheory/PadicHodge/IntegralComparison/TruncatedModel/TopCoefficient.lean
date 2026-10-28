import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.TopCoefficientEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Intrinsic
import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.OrdinaryCechCoefficientUnit

/-! # Top Coefficient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCoefficient

noncomputable section

/-! The original signed top-form input in the literal finite Witt
coefficient coordinates used by the native crystalline comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]

instance coefficients_preservesLimits :
    PreservesLimitsOfSize.{0,0} (OrdinarySectionMap.Ordinary.coefficients p k n) := by
  let : PreservesLimitsOfSize.{0,0}
      (ModuleCat.uliftFunctor.{2,1} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) :=
    preservesLimitsOfSize_of_univLE.{1,1} _
  dsimp only [OrdinarySectionMap.Ordinary.coefficients,
    Principal.Comparison.coefficients,
    Crystalline.RelativeResolution.coefficientFunctor]
  infer_instance

abbrev targetCoordinates := Small.OrdinaryCechCoefficientUnit.Ordinary.targetCoordinates
  (Truncated.Witt.Ring p k n) X (OrdinarySectionMap.Ordinary.coefficients p k n)

omit [Fintype k] [CharP k p] [X.left.IsSeparated] in
theorem ordinary_input (q : ℕ)
    (x : (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total (Truncated.Witt.Ring p k n) X).homology q) :
    (OrderedCech.ProjectionCoefficients.ordinaryHomologyIso
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X)
      (OrdinarySectionMap.Ordinary.coefficients p k n)
      (IntrinsicDeRham.CechComplex.Intrinsic.presheafComplex (Truncated.Witt.Ring p k n) X) q).hom
        (ULift.up.{2,1} (ULift.up.{1,0} x)) =
    homologyMap (targetCoordinates p k n X).hom q
      (Intrinsic.inputEquiv p k n X q x) := rfl

variable (g : ℕ) [SmoothOfRelativeDimension g X.hom]

abbrev map := IntrinsicOrdered.TopCoefficientEdge.Intrinsic.mappedTopMap (Truncated.Witt.Ring p k n) X g
  (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X)
  (OrdinarySectionMap.Ordinary.coefficients p k n)

def sourceInput (x : IntrinsicDeRham.TopEdge.Intrinsic.source (Truncated.Witt.Ring p k n) X
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) g) :=
  IntrinsicOrdered.TopCoefficientEdge.Intrinsic.sourceCoordinates (Truncated.Witt.Ring p k n) X g
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X)
    (OrdinarySectionMap.Ordinary.coefficients p k n)
    (ULift.up.{2,1} (ULift.up.{1,0} x))

omit [Fintype k] [CharP k p] [X.left.IsSeparated] in
theorem comparison (x : IntrinsicDeRham.TopEdge.Intrinsic.source (Truncated.Witt.Ring p k n) X
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) g) :
    homologyMap (map p k n X g) (g+g) (sourceInput p k n X g x) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g •
      homologyMap (OrderedCech.TotalProjection.map
        (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X)
        (OrderedCech.CoefficientTotal.mapped
          (OrdinarySectionMap.Ordinary.coefficients p k n)
          (IntrinsicDeRham.CechComplex.Intrinsic.presheafComplex (Truncated.Witt.Ring p k n) X))) (g+g)
        (homologyMap (targetCoordinates p k n X).hom (g+g)
          (Intrinsic.inputEquiv p k n X (g+g)
            (IntrinsicDeRham.TopEdge.Intrinsic.map (Truncated.Witt.Ring p k n) X
              (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) g x))) := by
  have h := ConcreteCategory.congr_hom
    (IntrinsicOrdered.TopCoefficientEdge.Intrinsic.comparison (Truncated.Witt.Ring p k n) X g
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X)
      (OrdinarySectionMap.Ordinary.coefficients p k n))
    (ULift.up.{2,1} (ULift.up.{1,0} x))
  have hi := ordinary_input p k n X (g+g)
    (IntrinsicDeRham.TopEdge.Intrinsic.map (Truncated.Witt.Ring p k n) X
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) g x)
  exact h.trans (congrArg (fun y =>
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g •
      homologyMap (OrderedCech.TotalProjection.map
        (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X)
        (OrderedCech.CoefficientTotal.mapped
          (OrdinarySectionMap.Ordinary.coefficients p k n)
          (IntrinsicDeRham.CechComplex.Intrinsic.presheafComplex (Truncated.Witt.Ring p k n) X))) (g+g) y) hi)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCoefficient
