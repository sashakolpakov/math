import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.BracketSpectralFunctions
import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.Killing
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! # Bracket Square Root -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.BracketSquareRoot.Construction

noncomputable section

/-! A positive self-adjoint bracket-preserving operator has an
invertible self-adjoint bracket-preserving square root. -/

theorem positive_bilinear_preserver_squareRoot
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    (B : L →L[ℝ] L →L[ℝ] L) (g : L →L[ℝ] L) (hsym : g.toLinearMap.IsSymmetric)
    (hpos : ∀ x : L, x ≠ 0 → 0 < inner ℝ (g x) x)
    (hB : ∀ x y, g (B x y) = B (g x) (g y)) :
    ∃ s : L ≃L[ℝ] L, s.toLinearMap.IsSymmetric ∧
      (∀ x : L, x ≠ 0 → 0 < inner ℝ (s x) x) ∧
      s.toContinuousLinearMap * s.toContinuousLinearMap = g ∧
        ∀ x y, s (B x y) = B (s x) (s y) := by
  let b := hsym.eigenvectorBasis (n := Module.finrank ℝ L) rfl
  let w := hsym.eigenvalues (n := Module.finrank ℝ L) rfl
  have hg (i : Fin (Module.finrank ℝ L)) : g (b i) = w i • b i :=
    hsym.apply_eigenvectorBasis rfl i
  have hw (i : Fin (Module.finrank ℝ L)) : 0 < w i := by
    have hi := hpos (b i) (b.toBasis.ne_zero i)
    rw [hg, real_inner_smul_left, b.inner_eq_one, mul_one] at hi
    exact hi
  let S := BasisSpectralOperator.Construction.basisSpectralEnd b.toBasis (fun i => Real.sqrt (w i))
  have hS : S * S = g.toLinearMap := BracketSpectralFunctions.Construction.positive_eigenbasis_sqrt_square b.toBasis g.toLinearMap w hg hw
  have hginj : Function.Injective g := by
    apply (injective_iff_map_eq_zero g).mpr
    intro x hx
    by_contra hne
    have hp := hpos x hne
    simp only [hx, inner_zero_left, lt_self_iff_false] at hp
  have hSinj : Function.Injective S := by
    intro x y hxy
    apply hginj
    change g.toLinearMap x = g.toLinearMap y
    rw [← hS]
    change S (S x) = S (S y)
    rw [hxy]
  let s : L ≃L[ℝ] L :=
    (LinearEquiv.ofBijective S ⟨hSinj, LinearMap.injective_iff_surjective.mp hSinj⟩).toContinuousLinearEquiv
  refine ⟨s, BasisSpectralOperator.Construction.basisSpectralEnd_isSymmetric b _, ?_, ?_, ?_⟩
  · exact BasisSpectralOperator.Construction.basisSpectralEnd_positive b _ (fun i => Real.sqrt_pos.mpr (hw i))
  · apply ContinuousLinearMap.ext
    intro x
    exact DFunLike.congr_fun hS x
  · exact BracketSpectralFunctions.Construction.positive_eigenbasis_sqrt_preserves (ContinuousBracketChange.Construction.finiteBilinearEquiv.symm B) b.toBasis
      g.toLinearMap w hg hw hB

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.BracketSquareRoot.Construction
