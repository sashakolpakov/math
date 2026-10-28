import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.DualNumber
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Basic

/-! # Tensor Evaluation -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.TensorEvaluation

noncomputable section

/-! Evaluation of a scalar-extended regular coefficient at a constant
dual-number point, including holomorphy of its infinitesimal coefficient. -/

open scoped TensorProduct

variable {A : Type*} [CommRing A] [Algebra ℂ A]

def dualTensorEvaluation (p : A →ₐ[ℂ] ℂ) : (DualNumber ℂ ⊗[ℂ] A) →ₐ[ℂ] DualNumber ℂ :=
  Algebra.TensorProduct.lift (AlgHom.id ℂ (DualNumber ℂ)) ((Algebra.ofId ℂ (DualNumber ℂ)).comp p)
    (fun _ _ => Commute.all _ _)

theorem dualTensorEvaluation_comp_left (p : A →ₐ[ℂ] ℂ) :
    (dualTensorEvaluation p).comp Algebra.TensorProduct.includeLeft = AlgHom.id ℂ (DualNumber ℂ) :=
  Algebra.TensorProduct.lift_comp_includeLeft _ _ _

theorem dualTensorEvaluation_comp_right (p : A →ₐ[ℂ] ℂ) :
    (dualTensorEvaluation p).comp Algebra.TensorProduct.includeRight = (Algebra.ofId ℂ (DualNumber ℂ)).comp p :=
  Algebra.TensorProduct.lift_comp_includeRight (AlgHom.id ℂ (DualNumber ℂ))
    ((Algebra.ofId ℂ (DualNumber ℂ)).comp p) (fun _ _ => Commute.all _ _)

theorem dualTensorEvaluation_tmul_snd (p : A →ₐ[ℂ] ℂ) (c : DualNumber ℂ) (a : A) :
    (dualTensorEvaluation p (c ⊗ₜ[ℂ] a)).snd = c.snd * p a := by
  simp [dualTensorEvaluation, Algebra.TensorProduct.lift_tmul,
    TrivSqZeroExt.algebraMap_eq_inl]

theorem dualTensorEvaluation_tmul_fst (p : A →ₐ[ℂ] ℂ) (c : DualNumber ℂ) (a : A) :
    (dualTensorEvaluation p (c ⊗ₜ[ℂ] a)).fst = c.fst * p a := by
  simp [dualTensorEvaluation, Algebra.TensorProduct.lift_tmul, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualTensorEvaluation_snd_differentiable {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    (p : V → (A →ₐ[ℂ] ℂ)) (hp : ∀ a, Differentiable ℂ (fun z => p z a))
    (u : DualNumber ℂ ⊗[ℂ] A) :
    Differentiable ℂ (fun z => (dualTensorEvaluation (p z) u).snd) := by
  induction u using TensorProduct.inductionOn with
  | tmul c a =>
    simpa only [dualTensorEvaluation_tmul_snd] using (hp a).const_mul c.snd
  | add u v hu hv =>
    simpa only [map_add, TrivSqZeroExt.snd_add] using hu.fun_add hv

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.TensorEvaluation
