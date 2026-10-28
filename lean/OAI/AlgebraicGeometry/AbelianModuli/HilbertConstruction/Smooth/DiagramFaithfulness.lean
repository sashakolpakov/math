import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineDiagramModel
import Mathlib.RingTheory.Flat.Basic

/-! # Diagram Faithfulness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth

noncomputable section

/-! Model elements embed in the original affine algebras, and the embeddings intertwine every arrow. -/

open TensorProduct

universe u v w

variable {R : Type u} [CommRing R] {I : Type v} {A : I → Type u}
variable [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable {J : Type w} {s t : J → I} {φ : ∀ j, A (s j) →ₐ[R] A (t j)}
variable (M : AffineDiagramModel.SmoothAffineDiagramModel R A s t φ)

def AffineDiagramModel.SmoothAffineDiagramModel.realization (i : I) : M.algebra i →+* A i :=
  (M.recovery i).symm.toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := M.coefficients) (A := R) (B := M.algebra i)).toRingHom

theorem AffineDiagramModel.SmoothAffineDiagramModel.realization_injective (i : I) : Function.Injective (M.realization i) :=
  (M.recovery i).symm.injective.comp
    (Algebra.TensorProduct.includeRight_injective
      (R := M.coefficients) (A := R) (B := M.algebra i) Subtype.val_injective)

theorem AffineDiagramModel.SmoothAffineDiagramModel.recovery_realization (i : I) (x : M.algebra i) :
    M.recovery i (M.realization i x) = (1 : R) ⊗ₜ[M.coefficients] x := by
  change M.recovery i ((M.recovery i).symm ((1 : R) ⊗ₜ[M.coefficients] x)) = _
  exact (M.recovery i).apply_symm_apply _

theorem AffineDiagramModel.SmoothAffineDiagramModel.realization_arrow (j : J) (x : M.algebra (s j)) :
    M.realization (t j) (M.arrow j x) = φ j (M.realization (s j) x) := by
  apply (M.recovery (t j)).injective
  rw [M.recovery_realization, M.recovery_naturality, M.recovery_realization]
  exact (Algebra.TensorProduct.map_tmul (AlgHom.id R R) (M.arrow j) (1 : R) x).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth
