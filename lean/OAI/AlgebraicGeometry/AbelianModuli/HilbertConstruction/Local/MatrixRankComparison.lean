import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CokernelSplittingEquation
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Matrix Rank Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.MatrixRankComparison

noncomputable section

/-! For a finite matrix over a local ring, flatness and a prescribed
rank at every prime are equivalent to flatness and the actual local
module rank. The argument supplies finite presentation explicitly. -/
universe u v w
variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {μ : Type v} {ν : Type w} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]

omit [DecidableEq ν] in
theorem localMatrixCokernel_rankAtStalk_iff_finrank (F : Matrix ν μ R) (k m : ℕ) :
    (Module.Flat R ((ν → R) ⧸ (Matrix.toLin' F).range) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R)
        ((ν → R) ⧸ (Matrix.toLin' F).range) p + k = m) ↔
    (Module.Flat R ((ν → R) ⧸ (Matrix.toLin' F).range) ∧
      Module.finrank R ((ν → R) ⧸ (Matrix.toLin' F).range) + k = m) := by
  have : Module.FinitePresentation R ((ν → R) ⧸ (Matrix.toLin' F).range) :=
    Module.finitePresentation_of_free_of_surjective (Matrix.toLin' F).range.mkQ
      (Matrix.toLin' F).range.mkQ_surjective (by
        rw [Submodule.ker_mkQ]
        exact Submodule.fg_range (Matrix.toLin' F))
  constructor
  · rintro ⟨hflat, hrank⟩
    let := hflat
    have : Module.Free R ((ν → R) ⧸ (Matrix.toLin' F).range) := Module.free_of_flat_of_isLocalRing
    exact ⟨hflat, by simpa only [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Nat.cast_id] using hrank (IsLocalRing.closedPoint R)⟩
  · rintro ⟨hflat, hrank⟩
    let := hflat
    have : Module.Free R ((ν → R) ⧸ (Matrix.toLin' F).range) := Module.free_of_flat_of_isLocalRing
    exact ⟨hflat, fun p => by simpa only [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Nat.cast_id] using hrank⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.MatrixRankComparison
