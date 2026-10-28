import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.GeometricComponents
import OAI.NumberTheory.PadicHodge.IntegralComparison.PermutationPolynomial
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.EtaleDegreeZero

/-! # Polynomial -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.Polynomial.Etale

noncomputable section

/-! The original geometric étale Frobenius of a finite étale affine scheme has the actual Witt Frobenius polynomial. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

variable (p a : ℕ) [Fact p.Prime] (k A : Type u) [Field k] [Fintype k] [CommRing A] [Algebra k A]
  [CharP k p] [Nontrivial A] [Module.Finite k A] [Algebra.Etale k A]
  (hcard : Fintype.card k = p ^ a)

local notation "Ω" => AlgebraicClosure k
local notation "T" => Ω ⊗[k] A
local notation "f" => Spec.map (CommRingCat.ofHom (algebraMap k A))
local notation "Y" => OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Geometry.geometricFiber (L := Ω) f

local instance : IsFinite f :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
local instance : Fintype (PrimeSpectrum T) :=
  let := WittSplitting.finite_index k A
  Fintype.ofFinite _
local instance : DecidableEq (PrimeSpectrum T) := Classical.decEq _
local instance : Fintype (_root_.ConnectedComponents Y) := Fintype.ofFinite _
local instance : DecidableEq (_root_.ConnectedComponents Y) := Classical.decEq _

theorem polynomial : SmoothProper.EtaleDegreeZero.polynomial p a k hcard f =
    FrobeniusPolynomial.polynomial p k A := by
  exact (PermutationPolynomial.Equivalence.polynomial
    (WittPermutation.permutation k A (FrobeniusPolynomial.frobenius p k A))
    (SmoothProper.EtaleDegreeZero.permutation p a k hcard f)
    (GeometricComponents.equiv k A)
    (GeometricComponents.frobenius k A p a hcard)).symm

theorem charpoly (ℓ : ℕ) [Fact ℓ.Prime] :
    (Interfaces.etaleGeometricFrobenius ℓ p a k hcard f 0).charpoly =
      (FrobeniusPolynomial.polynomial p k A).map (Int.castRingHom ℚ_[ℓ]) := by
  rw [SmoothProper.EtaleDegreeZero.charpoly, polynomial p a k A hcard]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.Polynomial.Etale
