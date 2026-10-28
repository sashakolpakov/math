import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.SmoothProperVanishing
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DegreeZero

/-! # Smooth Proper -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.SmoothProper.Comparison

noncomputable section

/-! All-degree comparison on the original cohomology and Frobenius for affine smooth proper projective schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p ℓ a : ℕ) [Fact p.Prime] [Fact ℓ.Prime]
  (k : Type u) [Field k] [Fintype k] [CharP k p]
  (hcard : Fintype.card k = p ^ a)
  {X : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (CommRingCat.of k))
  [IsProper f] [Smooth f]

theorem comparison (hprojective : Projectivity.Construction.ProjectiveOver k f) (i : ℕ) :
    ∃ (hcrys : FiniteDimensional (FractionRing (WittVector p k)) (Interfaces.CrystallineCohomology p k f i))
      (het : FiniteDimensional ℚ_[ℓ] (Interfaces.EtaleCohomology ℓ k f i)),
      letI := hcrys
      letI := het
      ∃ P : Polynomial ℤ, P.Monic ∧
        (Interfaces.crystallineQFrobenius p a k hcard f i).charpoly =
          P.map (Int.castRingHom (FractionRing (WittVector p k))) ∧
        (Interfaces.etaleGeometricFrobenius ℓ p a k hcard f i).charpoly = P.map (Int.castRingHom ℚ_[ℓ]) := by
  cases i with
  | zero => exact SmoothProper.DegreeZero.Comparison.comparison p ℓ a k hcard f hprojective
  | succ i =>
    let : IsAffine (Over.mk f).left := inferInstanceAs (IsAffine X)
    let : IsProper (Over.mk f).hom := inferInstanceAs (IsProper f)
    let : Smooth (Over.mk f).hom := inferInstanceAs (Smooth f)
    let : Subsingleton (Interfaces.CrystallineCohomology p k f (i + 1)) :=
      SmoothProperVanishing.crystalline p k (Over.mk f) hprojective i
    let : Subsingleton (Interfaces.EtaleCohomology ℓ k f (i + 1)) :=
      SmoothProperVanishing.etale p k (Over.mk f) hprojective ℓ i
    refine ⟨inferInstance, inferInstance, 1, Polynomial.monic_one, ?_, ?_⟩
    · have h : Interfaces.crystallineQFrobenius p a k hcard f (i + 1) = 0 := Subsingleton.elim _ _
      rw [h, LinearMap.charpoly_zero, Module.finrank_zero_of_subsingleton, pow_zero, Polynomial.map_one]
    · have h : Interfaces.etaleGeometricFrobenius ℓ p a k hcard f (i + 1) = 0 := Subsingleton.elim _ _
      rw [h, LinearMap.charpoly_zero, Module.finrank_zero_of_subsingleton, pow_zero, Polynomial.map_one]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.SmoothProper.Comparison
