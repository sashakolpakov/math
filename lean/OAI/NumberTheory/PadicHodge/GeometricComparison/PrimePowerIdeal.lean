import OAI.NumberTheory.PadicHodge.GeometricComparison.IdealQuotientMaps

/-! # Prime Power Ideal -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.PrimePowerIdeal.PrimePowerIdealSheaf

noncomputable section

/-! The original prime-power ideals on affine section rings form an ideal
sheaf, whose closed-subscheme charts are their actual quotient spectra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable (X : Scheme.{u}) (p n : ℕ)

def ideal : X.IdealSheafData where
  ideal U := (Ideal.span {(p : Γ(X, U.val))}) ^ (n + 1)
  map_ideal_basicOpen U a := by
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast]
    rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.PrimePowerIdeal.PrimePowerIdealSheaf
