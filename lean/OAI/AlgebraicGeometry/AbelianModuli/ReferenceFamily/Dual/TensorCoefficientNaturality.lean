import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TransitionDerivationLaws
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.Derivation

/-! # Tensor Coefficient Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorCoefficientNaturality

noncomputable section

/-! The tensor-coordinate equivalence retains arbitrary coefficient
maps. Actual commuting tensor transitions therefore restrict derivations. -/

open scoped TensorProduct

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

local instance dualTensorCoefficientNaturality_sourceCommRing : CommRing (DualNumber k ⊗[k] A) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := A)

local instance dualTensorCoefficientNaturality_targetCommRing : CommRing (DualNumber k ⊗[k] B) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := B)

theorem dualTensorCoefficientEquiv_natural (q : A →ₐ[k] B) (u : DualNumber k ⊗[k] A) :
    NumberCoefficients.dualTensorCoefficientEquiv k B (Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) q u) =
      NumberCoefficients.dualNumberAlgMap q (NumberCoefficients.dualTensorCoefficientEquiv k A u) := by
  induction u using TensorProduct.inductionOn with
  | tmul c a =>
    change NumberCoefficients.dualTensorCoefficients k B (c ⊗ₜ[k] q a) = NumberCoefficients.dualNumberAlgMap q (NumberCoefficients.dualTensorCoefficients k A (c ⊗ₜ[k] a))
    rw [NumberCoefficients.dualTensorCoefficients_tmul, NumberCoefficients.dualTensorCoefficients_tmul]
    apply TrivSqZeroExt.ext
    · exact (q.toLinearMap.map_smul c.fst a).symm
    · exact (q.toLinearMap.map_smul c.snd a).symm
  | add u v hu hv => simp only [map_add, hu, hv]

theorem dualTensorTransitionCoordinates_natural (q : A →ₐ[k] B)
    (e : (DualNumber k ⊗[k] A) ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A))
    (f : (DualNumber k ⊗[k] B) ≃ₐ[DualNumber k] (DualNumber k ⊗[k] B))
    (h : (Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) q).comp e.toAlgHom =
      f.toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) q)) :
    (NumberCoefficients.dualNumberAlgMap q).comp (CoefficientLiftTensorMap.dualTensorTransitionCoordinates e).toAlgHom =
      (CoefficientLiftTensorMap.dualTensorTransitionCoordinates f).toAlgHom.comp (NumberCoefficients.dualNumberAlgMap q) := by
  let C := NumberCoefficients.dualTensorCoefficientEquiv k A
  let D := NumberCoefficients.dualTensorCoefficientEquiv k B
  let M := Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) q
  apply AlgHom.ext
  intro u
  have hm : M (C.symm u) = D.symm (NumberCoefficients.dualNumberAlgMap q u) := by
    apply D.injective
    exact (dualTensorCoefficientEquiv_natural q (C.symm u)).trans
      ((congrArg (NumberCoefficients.dualNumberAlgMap q) (C.apply_symm_apply u)).trans (D.apply_symm_apply _).symm)
  change NumberCoefficients.dualNumberAlgMap q (C (e (C.symm u))) = D (f (D.symm (NumberCoefficients.dualNumberAlgMap q u)))
  calc
    NumberCoefficients.dualNumberAlgMap q (C (e (C.symm u))) = D (M (e (C.symm u))) :=
      (dualTensorCoefficientEquiv_natural q (e (C.symm u))).symm
    _ = D (f (M (C.symm u))) := congrArg D (AlgHom.congr_fun h (C.symm u))
    _ = D (f (D.symm (NumberCoefficients.dualNumberAlgMap q u))) := by rw [hm]

theorem dualTensorTransitionDerivation_natural (q : A →ₐ[k] B)
    (e : (DualNumber k ⊗[k] A) ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A))
    (f : (DualNumber k ⊗[k] B) ≃ₐ[DualNumber k] (DualNumber k ⊗[k] B))
    (he : ∀ u, TensorReduction.dualTensorReduction k A (e u) = TensorReduction.dualTensorReduction k A u)
    (hf : ∀ u, TensorReduction.dualTensorReduction k B (f u) = TensorReduction.dualTensorReduction k B u)
    (h : (Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) q).comp e.toAlgHom =
      f.toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) q)) (a : A) :
    q (TransitionDerivationLaws.dualTensorTransitionDerivation e he a) = TransitionDerivationLaws.dualTensorTransitionDerivation f hf (q a) :=
  Derivation.dualIdentityDerivation_natural q (CoefficientLiftTensorMap.dualTensorTransitionCoordinates e).toAlgHom
    (CoefficientLiftTensorMap.dualTensorTransitionCoordinates f).toAlgHom
    (CoefficientLiftTensorMap.dualTensorTransitionCoordinates_reduction e he) (CoefficientLiftTensorMap.dualTensorTransitionCoordinates_reduction f hf)
    (dualTensorTransitionCoordinates_natural q e f h) a

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorCoefficientNaturality
