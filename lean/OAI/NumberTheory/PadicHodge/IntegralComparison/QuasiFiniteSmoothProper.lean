import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.SmoothProper
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Quasi Finite Smooth Proper -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.QuasiFiniteSmoothProper.Comparison

noncomputable section

/-! The original all-degree comparison for smooth proper projective schemes with zero-dimensional fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p ℓ a : ℕ) [Fact p.Prime] [Fact ℓ.Prime]
  (k : Type u) [Field k] [Fintype k] [CharP k p]
  (hcard : Fintype.card k = p ^ a)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [Smooth f]

theorem comparison [LocallyQuasiFinite f] (hprojective : Projectivity.Construction.ProjectiveOver k f) (i : ℕ) :
    ∃ (hcrys : FiniteDimensional (FractionRing (WittVector p k)) (Interfaces.CrystallineCohomology p k f i))
      (het : FiniteDimensional ℚ_[ℓ] (Interfaces.EtaleCohomology ℓ k f i)),
      letI := hcrys
      letI := het
      ∃ P : Polynomial ℤ, P.Monic ∧
        (Interfaces.crystallineQFrobenius p a k hcard f i).charpoly =
          P.map (Int.castRingHom (FractionRing (WittVector p k))) ∧
        (Interfaces.etaleGeometricFrobenius ℓ p a k hcard f i).charpoly = P.map (Int.castRingHom ℚ_[ℓ]) := by
  let : IsFinite f := IsFinite.of_isProper_of_locallyQuasiFinite f
  let : IsAffine X := isAffine_of_isAffineHom f
  exact Affine.SmoothProper.Comparison.comparison p ℓ a k hcard f hprojective i

theorem finiteSpace [Finite X] (hprojective : Projectivity.Construction.ProjectiveOver k f) (i : ℕ) :
    ∃ (hcrys : FiniteDimensional (FractionRing (WittVector p k)) (Interfaces.CrystallineCohomology p k f i))
      (het : FiniteDimensional ℚ_[ℓ] (Interfaces.EtaleCohomology ℓ k f i)),
      letI := hcrys
      letI := het
      ∃ P : Polynomial ℤ, P.Monic ∧
        (Interfaces.crystallineQFrobenius p a k hcard f i).charpoly =
          P.map (Int.castRingHom (FractionRing (WittVector p k))) ∧
        (Interfaces.etaleGeometricFrobenius ℓ p a k hcard f i).charpoly = P.map (Int.castRingHom ℚ_[ℓ]) := by
  let : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f
    (fun _ => Set.toFinite _)
  exact comparison p ℓ a k hcard f hprojective i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.QuasiFiniteSmoothProper.Comparison
