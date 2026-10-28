import OAI.RepresentationTheory.Weil.AdelicSplitting.Integral

/-! # Integral Squares -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.IntegralSquares.CM

noncomputable section

/-! A square root and its inverse are integral whenever their squares
are integral in the actual finite valuation ring. -/

open scoped _root_.NumberField
open OAI.RepresentationTheory.Weil.AdelicSplitting.Integral.Construction

variable (F : Type*) [Field F] [NumberField F]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))

theorem of_square (x : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v))
    (h : x ^ 2 ∈ RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v)) :
    x ∈ RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) := by
  change Valued.v x ≤ 1
  change Valued.v (x ^ 2) ≤ 1 at h
  rw [map_pow] at h
  exact (pow_le_one_iff_of_nonneg zero_le (by decide : (2 : ℕ) ≠ 0)).mp h

theorem inverse_of_square (x : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) {d : F}
    (hx : x ^ 2 = RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d)
    (h : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d⁻¹ ∈ RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v)) :
    x⁻¹ ∈ RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) := by
  apply of_square F v
  rw [inv_pow, hx, ← map_inv₀]
  exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.IntegralSquares.CM
