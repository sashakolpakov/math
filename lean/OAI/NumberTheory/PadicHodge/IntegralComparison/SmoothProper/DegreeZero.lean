import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.NonemptyDegreeZero
import OAI.NumberTheory.PadicHodge.IntegralComparison.EmptyDegreeZero

/-! # Degree Zero -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DegreeZero.Comparison

noncomputable section

/-! Unconditional degree-zero Katz–Messing comparison on the original cohomology and Frobenius. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p ℓ a : ℕ) [Fact p.Prime] [Fact ℓ.Prime]
  (k : Type u) [Field k] [Fintype k] [CharP k p] (hcard : Fintype.card k = p ^ a)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [Smooth f]
  (hprojective : Projectivity.Construction.ProjectiveOver k f)

include hprojective in
theorem comparison :
    ∃ (hcrys : FiniteDimensional (FractionRing (WittVector p k)) (Interfaces.CrystallineCohomology p k f 0))
      (het : FiniteDimensional ℚ_[ℓ] (Interfaces.EtaleCohomology ℓ k f 0)),
      letI := hcrys
      letI := het
      ∃ P : Polynomial ℤ, P.Monic ∧
        (Interfaces.crystallineQFrobenius p a k hcard f 0).charpoly =
          P.map (Int.castRingHom (FractionRing (WittVector p k))) ∧
        (Interfaces.etaleGeometricFrobenius ℓ p a k hcard f 0).charpoly = P.map (Int.castRingHom ℚ_[ℓ]) := by
  let : IsProper (Over.mk f).hom := inferInstanceAs (IsProper f)
  let : Smooth (Over.mk f).hom := inferInstanceAs (Smooth f)
  rcases isEmpty_or_nonempty X with h | h
  · let : IsEmpty (Over.mk f).left := h
    exact EmptyDegreeZero.Comparison.comparison p k (Over.mk f) hprojective a hcard ℓ
  · let : Nonempty (Over.mk f).left := h
    exact NonemptyDegreeZero.Comparison.comparison p k (Over.mk f) hprojective a hcard ℓ

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DegreeZero.Comparison
