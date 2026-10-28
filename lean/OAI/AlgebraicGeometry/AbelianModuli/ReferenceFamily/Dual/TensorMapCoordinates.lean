import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientLiftTensorMap
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.MapConstantReduction

/-! # Tensor Map Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorMapCoordinates

noncomputable section

/-! Literal maps over the dual-number base retain that parameter in
coefficient coordinates. Their action on lift differences is the
original reduced coefficient map. -/

open scoped TensorProduct

variable {k A B : Type} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B]

local instance dualTensorMapCoordinates_sourceCommRing : CommRing (DualNumber k ⊗[k] A) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := A)

local instance dualTensorMapCoordinates_targetCommRing : CommRing (DualNumber k ⊗[k] B) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := B)

variable (m : (DualNumber k ⊗[k] A) →ₐ[DualNumber k] (DualNumber k ⊗[k] B))

def dualTensorMapCoordinates : DualNumber A →ₐ[k] DualNumber B :=
  (NumberCoefficients.dualTensorCoefficientEquiv k B).toAlgHom.comp
    ((m.restrictScalars k).comp (NumberCoefficients.dualTensorCoefficientEquiv k A).symm.toAlgHom)

theorem dualTensorMapCoordinates_eps :
    dualTensorMapCoordinates m DualNumber.eps = DualNumber.eps := by
  let C := NumberCoefficients.dualTensorCoefficientEquiv k A
  have hi : C.symm DualNumber.eps = algebraMap (DualNumber k) (DualNumber k ⊗[k] A) DualNumber.eps := by
    apply C.injective
    exact (C.apply_symm_apply _).trans (CoefficientLiftTensorMap.dualTensorCoefficientEquiv_eps (k := k) (A := A)).symm
  change NumberCoefficients.dualTensorCoefficientEquiv k B (m (C.symm DualNumber.eps)) = DualNumber.eps
  rw [hi, m.commutes]
  exact CoefficientLiftTensorMap.dualTensorCoefficientEquiv_eps

theorem dualTensorMapCoordinates_reduction (q : A →ₐ[k] B)
    (h : ∀ t, TensorReduction.dualTensorReduction k B (m t) = q (TensorReduction.dualTensorReduction k A t))
    (u : DualNumber A) :
    (dualTensorMapCoordinates m u).fst = q u.fst := by
  change TensorReduction.dualTensorReduction k B (m ((NumberCoefficients.dualTensorCoefficientEquiv k A).symm u)) = q u.fst
  rw [h]
  change q ((NumberCoefficients.dualTensorCoefficientEquiv k A) ((NumberCoefficients.dualTensorCoefficientEquiv k A).symm u)).fst = q u.fst
  rw [AlgEquiv.apply_symm_apply]

theorem dualTensorMapCoordinates_difference (q : A →ₐ[k] B)
    (h : ∀ t, TensorReduction.dualTensorReduction k B (m t) = q (TensorReduction.dualTensorReduction k A t))
    (u v : DualNumber A) (huv : u.fst = v.fst) :
    (dualTensorMapCoordinates m u).snd - (dualTensorMapCoordinates m v).snd = q (u.snd - v.snd) :=
  MapConstantReduction.dualMap_sameReduction_difference q (dualTensorMapCoordinates m)
    (dualTensorMapCoordinates_reduction m q h) (dualTensorMapCoordinates_eps m) u v huv

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorMapCoordinates
