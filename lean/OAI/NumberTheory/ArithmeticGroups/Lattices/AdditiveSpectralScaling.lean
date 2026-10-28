import OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialSpectralFunctions
import OAI.NumberTheory.ArithmeticGroups.Lattices.JordanScaling

/-! # Additive Spectral Scaling -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.AdditiveSpectralScaling.Construction

noncomputable section

/-! An additive change of eigenvalues transports bracket scaling by the
same additive map. -/

open scoped Classical
open _root_.Module LieAlgebra

attribute [local instance] LieRing.ofAssociativeRing

theorem additive_spectral_bracket_scaling
    {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V] [Fintype ι]
    (b : Module.Basis ι k V) (S T A : Module.End k V) (w : ι → k) (ψ : k →+ k)
    (hS : ∀ i, S (b i) = w i • b i)
    (hT : ∀ i, T (b i) = ψ (w i) • b i)
    (a : k) (hscale : ⁅S, A⁆ = a • A) : ⁅T, A⁆ = ψ a • A := by
  apply PolynomialSpectralFunctions.Construction.eigenvalue_function_on_eigenvector b.end (ad k _ S) (ad k _ T)
    (fun ij => w ij.1 - w ij.2) ψ _ _ A a hscale
  · rintro ⟨i, j⟩
    exact b.lie_end_of_apply_eq_smul w S hS i j
  · rintro ⟨i, j⟩
    rw [ad_apply, ← Module.End.instLieRingModule_eq,
      b.lie_end_of_apply_eq_smul (fun i => ψ (w i)) T hT, map_sub]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.AdditiveSpectralScaling.Construction
