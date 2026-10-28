import OAI.NumberTheory.ArithmeticGroups.Lattices.ContractingLocalHomeomorphism
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! # Contracting Inverse Function Theorem -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ContractingInverseFunctionTheorem.Construction

noncomputable section

/-! A globally contracting equivariant map with an invertible derivative
at its fixed point is a global homeomorphism. -/

open Filter
open scoped _root_.Topology

theorem exists_homeomorph_of_contracting_strict_derivative
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : Continuous f) (e : E ≃L[ℝ] F) (x₀ : E)
    (hdf : HasStrictFDerivAt f e.toContinuousLinearMap x₀)
    (a : ι → E ≃ₜ E) (b : ι → F ≃ₜ F)
    (heq : ∀ t x, f (a t x) = b t (f x)) (l : Filter ι) [NeBot l]
    (ha : ∀ x, Tendsto (fun t => a t x) l (𝓝 x₀))
    (hb : ∀ y, Tendsto (fun t => b t y) l (𝓝 (f x₀))) :
    ∃ h : E ≃ₜ F, (h : E → F) = f :=
  ContractingLocalHomeomorphism.Construction.exists_homeomorph_of_contracting_local_homeomorphism f hf
    (hdf.toOpenPartialHomeomorph f) hdf.toOpenPartialHomeomorph_coe x₀
    hdf.mem_toOpenPartialHomeomorph_source a b heq l ha hb

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ContractingInverseFunctionTheorem.Construction
