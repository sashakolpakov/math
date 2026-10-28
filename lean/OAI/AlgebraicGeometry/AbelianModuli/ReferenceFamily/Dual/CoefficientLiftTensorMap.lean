import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.Derivation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorReductionEquiv

/-! # Coefficient Lift Tensor Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientLiftTensorMap

noncomputable section

section

/-! Actual automorphisms of the scalar-extended affine product over the
dual-number base become unique derivation automorphisms in coefficients,
when their prescribed special-fiber map is the identity. -/

open scoped TensorProduct

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

local instance dualTensorTransitionCoordinates_commRing : CommRing (DualNumber k ⊗[k] A) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := A)

theorem dualTensorCoefficientEquiv_base (c : DualNumber k) :
    NumberCoefficients.dualTensorCoefficientEquiv k A (algebraMap (DualNumber k) (DualNumber k ⊗[k] A) c) =
      NumberCoefficients.dualNumberRingMap (algebraMap k A) c := by
  change NumberCoefficients.dualTensorCoefficients k A (c ⊗ₜ[k] (1 : A)) = _
  rw [NumberCoefficients.dualTensorCoefficients_tmul]
  apply TrivSqZeroExt.ext
  · change c.fst • (1 : A) = algebraMap k A c.fst
    rw [Algebra.smul_def, mul_one]
  · change c.snd • (1 : A) = algebraMap k A c.snd
    rw [Algebra.smul_def, mul_one]

theorem dualTensorCoefficientEquiv_eps :
    NumberCoefficients.dualTensorCoefficientEquiv k A
      (algebraMap (DualNumber k) (DualNumber k ⊗[k] A) DualNumber.eps) = DualNumber.eps := by
  rw [dualTensorCoefficientEquiv_base]
  apply TrivSqZeroExt.ext
  · change algebraMap k A 0 = 0
    exact map_zero _
  · change algebraMap k A 1 = 1
    exact map_one _

def dualTensorTransitionCoordinates
    (e : (DualNumber k ⊗[k] A) ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A)) :
    DualNumber A ≃ₐ[k] DualNumber A :=
  (NumberCoefficients.dualTensorCoefficientEquiv k A).symm.trans
    ((e.restrictScalars k).trans (NumberCoefficients.dualTensorCoefficientEquiv k A))

theorem dualTensorTransitionCoordinates_eps
    (e : (DualNumber k ⊗[k] A) ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A)) :
    dualTensorTransitionCoordinates e DualNumber.eps = DualNumber.eps := by
  let C := NumberCoefficients.dualTensorCoefficientEquiv k A
  have hi : C.symm DualNumber.eps = algebraMap (DualNumber k) (DualNumber k ⊗[k] A) DualNumber.eps := by
    apply C.injective
    exact (C.apply_symm_apply _).trans (dualTensorCoefficientEquiv_eps (k := k) (A := A)).symm
  change C (e (C.symm DualNumber.eps)) = DualNumber.eps
  rw [hi, e.commutes]
  exact dualTensorCoefficientEquiv_eps

theorem dualTensorTransitionCoordinates_reduction
    (e : (DualNumber k ⊗[k] A) ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A))
    (hred : ∀ u, TensorReduction.dualTensorReduction k A (e u) = TensorReduction.dualTensorReduction k A u) (u : DualNumber A) :
    (dualTensorTransitionCoordinates e u).fst = u.fst := by
  let C := NumberCoefficients.dualTensorCoefficientEquiv k A
  change TensorReduction.dualTensorReduction k A (e (C.symm u)) = u.fst
  rw [hred]
  change (C (C.symm u)).fst = u.fst
  rw [C.apply_symm_apply]

theorem exists_unique_dualTensorTransition_derivation
    (e : (DualNumber k ⊗[k] A) ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A))
    (hred : ∀ u, TensorReduction.dualTensorReduction k A (e u) = TensorReduction.dualTensorReduction k A u) :
    ∃! d : Derivation k A A,
      (Dual.Derivation.dualDerivationAutomorphism d).toAlgHom = (dualTensorTransitionCoordinates e).toAlgHom := by
  let f := (dualTensorTransitionCoordinates e).toAlgHom
  have hf : ∀ u, (f u).fst = u.fst := dualTensorTransitionCoordinates_reduction e hred
  let d := Dual.Derivation.dualIdentityDerivation f hf
  refine ⟨d, Dual.Derivation.dualDerivationAutomorphism_recover f hf (dualTensorTransitionCoordinates_eps e), ?_⟩
  intro d' hd'
  apply Derivation.ext
  intro a
  have he := congrArg (fun t : DualNumber A →ₐ[k] DualNumber A => (t (TrivSqZeroExt.inl a)).snd) hd'
  change d' a + 0 = (f (TrivSqZeroExt.inl a)).snd at he
  rw [add_zero] at he
  exact he

end

/-! An actual coefficient-valued dual-number lift gives a map to the
constant tensor product over the full dual-number base. Its two original
coefficients and reduction are retained. -/

open scoped TensorProduct

variable (k R S B : Type) [CommRing k] [CommRing R] [CommRing S] [CommRing B]
    [Algebra k S] [Algebra k B] [Algebra R S] [Algebra R (DualNumber k)]

local instance dualLiftTensor_commRing : CommRing (DualNumber k ⊗[k] B) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := B)

variable [Algebra R (DualNumber k ⊗[k] B)]
    (hRT : ∀ r : R, algebraMap R (DualNumber k ⊗[k] B) r =
      algebraMap (DualNumber k) (DualNumber k ⊗[k] B) (algebraMap R (DualNumber k) r))
    (f : S →ₐ[k] DualNumber B)
    (hf : ∀ r : R, f (algebraMap R S r) =
      NumberCoefficients.dualNumberRingMap (algebraMap k B) (algebraMap R (DualNumber k) r))

def dualCoefficientLiftTensorMap : S →ₐ[R] (DualNumber k ⊗[k] B) where
  __ := ((NumberCoefficients.dualTensorCoefficientEquiv k B).symm.toAlgHom.comp f).toRingHom
  commutes' r := by
    apply (NumberCoefficients.dualTensorCoefficientEquiv k B).injective
    change (NumberCoefficients.dualTensorCoefficientEquiv k B)
        ((NumberCoefficients.dualTensorCoefficientEquiv k B).symm (f (algebraMap R S r))) = _
    rw [AlgEquiv.apply_symm_apply,
      hRT, dualTensorCoefficientEquiv_base]
    exact hf r

theorem dualCoefficientLiftTensorMap_coefficients (s : S) :
    NumberCoefficients.dualTensorCoefficientEquiv k B (dualCoefficientLiftTensorMap k R S B hRT f hf s) = f s :=
  (NumberCoefficients.dualTensorCoefficientEquiv k B).apply_symm_apply (f s)

theorem dualCoefficientLiftTensorMap_reduction (s : S) :
    TensorReduction.dualTensorReduction k B (dualCoefficientLiftTensorMap k R S B hRT f hf s) = (f s).fst :=
  congrArg TrivSqZeroExt.fst (dualCoefficientLiftTensorMap_coefficients k R S B hRT f hf s)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientLiftTensorMap
