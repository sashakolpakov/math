import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.ReductionIdentity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TransitionDerivationLaws

/-! # Transition Derivation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.TransitionDerivation

noncomputable section

/-! Actual automorphisms of affine products that act identically on
the scheme special fiber have uniquely determined derivation coefficients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (k : Type) [Field k] (X : Over (Spec (.of k))) [IsAffine X.left]

local instance affineProductTransitionDerivation_tensorCommRing :
    CommRing (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X)

variable (e : (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X ≅ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X)
    (he : (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map e.hom =
      𝟙 ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj ((Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X)))

def affineProductTransitionDerivation :
    Derivation k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) :=
  Dual.TransitionDerivationLaws.dualTensorTransitionDerivation (Coordinates.affineProductAutomorphismAlgebra k X e)
    (ReductionIdentity.affineProductAutomorphismAlgebra_reduction k X e he)

theorem affineProductTransitionDerivation_coordinates :
    (Dual.Derivation.dualDerivationAutomorphism (affineProductTransitionDerivation k X e he)).toAlgHom =
      (Dual.CoefficientLiftTensorMap.dualTensorTransitionCoordinates (Coordinates.affineProductAutomorphismAlgebra k X e)).toAlgHom :=
  Dual.Derivation.dualDerivationAutomorphism_recover
    (Dual.CoefficientLiftTensorMap.dualTensorTransitionCoordinates (Coordinates.affineProductAutomorphismAlgebra k X e)).toAlgHom
    (Dual.CoefficientLiftTensorMap.dualTensorTransitionCoordinates_reduction (Coordinates.affineProductAutomorphismAlgebra k X e)
      (ReductionIdentity.affineProductAutomorphismAlgebra_reduction k X e he))
    (Dual.CoefficientLiftTensorMap.dualTensorTransitionCoordinates_eps (Coordinates.affineProductAutomorphismAlgebra k X e))

theorem affineProductAutomorphism_normalForm (u : DualNumber (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X)) :
    Dual.CoefficientLiftTensorMap.dualTensorTransitionCoordinates (Coordinates.affineProductAutomorphismAlgebra k X e) u =
      (u.fst, affineProductTransitionDerivation k X e he u.fst + u.snd) :=
  (AlgHom.congr_fun (affineProductTransitionDerivation_coordinates k X e he) u).symm.trans
    (Dual.Derivation.dualDerivationAutomorphism_apply (affineProductTransitionDerivation k X e he) u)

include he in
theorem exists_unique_affineProductTransition_derivation :
    ∃! d : Derivation k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X),
      (Dual.Derivation.dualDerivationAutomorphism d).toAlgHom =
        (Dual.CoefficientLiftTensorMap.dualTensorTransitionCoordinates (Coordinates.affineProductAutomorphismAlgebra k X e)).toAlgHom :=
  Dual.CoefficientLiftTensorMap.exists_unique_dualTensorTransition_derivation (Coordinates.affineProductAutomorphismAlgebra k X e)
    (ReductionIdentity.affineProductAutomorphismAlgebra_reduction k X e he)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.TransitionDerivation
