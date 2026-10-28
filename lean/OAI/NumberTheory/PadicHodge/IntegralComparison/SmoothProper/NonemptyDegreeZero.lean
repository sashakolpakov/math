import OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.CrystallinePolynomial
import OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.CrystallineBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.EtaleDegreeZero
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.Polynomial

/-! # Nonempty Degree Zero -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.NonemptyDegreeZero.Comparison

noncomputable section

/-! A common monic integer polynomial for the original degree-zero cohomology and Frobenius of every nonempty smooth proper projective scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] PeriodInvariants.WittAlgebraFunctor.wittAlgebra

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom] [Nonempty X.left]
  (hprojective : Projectivity.Construction.ProjectiveOver k X.hom)

local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.GlobalFunctionAlgebra.algebra k X
local notation "K" => FractionRing (WittVector p k)

def polynomial : Polynomial ℤ := by
  let := GlobalFunctionAlgebra.nontrivial k X
  let := GlobalFunctionAlgebra.module_finite k X hprojective
  let := GlobalFunctionAlgebra.etale k X p hprojective
  exact FiniteEtale.FrobeniusPolynomial.polynomial p k A

theorem monic : (polynomial p k X hprojective).Monic := by
  let := GlobalFunctionAlgebra.nontrivial k X
  let := GlobalFunctionAlgebra.module_finite k X hprojective
  let := GlobalFunctionAlgebra.etale k X p hprojective
  exact FiniteEtale.FrobeniusPolynomial.monic p k A

variable (a : ℕ) (hcard : Fintype.card k = p ^ a)

theorem crystalline :
    letI := CrystallineFiniteness.rational p k X hprojective 0
    (Global.CrystallineFrobenius.rationalFrobenius p k X a hcard 0).charpoly =
      (polynomial p k X hprojective).map (Int.castRingHom K) := by
  let := CrystallineFiniteness.rational p k X hprojective 0
  let := GlobalFunctionAlgebra.nontrivial k X
  let := GlobalFunctionAlgebra.module_finite k X hprojective
  let := GlobalFunctionAlgebra.etale k X p hprojective
  exact (GlobalFunction.CrystallinePolynomial.charpoly p k X hprojective a hcard).trans
    (FiniteEtale.FrobeniusPolynomial.rational p k A)

theorem etale (ℓ : ℕ) [Fact ℓ.Prime] :
    (Interfaces.etaleGeometricFrobenius ℓ p a k hcard X.hom 0).charpoly =
      (polynomial p k X hprojective).map (Int.castRingHom ℚ_[ℓ]) := by
  let := GlobalFunctionAlgebra.nontrivial k X
  let := GlobalFunctionAlgebra.module_finite k X hprojective
  let := GlobalFunctionAlgebra.etale k X p hprojective
  exact (GlobalFunction.EtaleDegreeZero.charpoly k X hprojective ℓ p a hcard).trans
    (FiniteEtale.Polynomial.Etale.charpoly p a k A hcard ℓ)

include hprojective in
theorem comparison (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ (hcrys : FiniteDimensional K (Witt.Crystalline.rationalCohomology p k X 0))
      (het : FiniteDimensional ℚ_[ℓ] (Interfaces.EtaleCohomology ℓ k X.hom 0)),
      letI := hcrys
      letI := het
      ∃ P : Polynomial ℤ, P.Monic ∧
        (Global.CrystallineFrobenius.rationalFrobenius p k X a hcard 0).charpoly = P.map (Int.castRingHom K) ∧
        (Interfaces.etaleGeometricFrobenius ℓ p a k hcard X.hom 0).charpoly = P.map (Int.castRingHom ℚ_[ℓ]) :=
  ⟨CrystallineFiniteness.rational p k X hprojective 0,
    EtaleDegreeZero.finite k X.hom ℓ,
    polynomial p k X hprojective, monic p k X hprojective,
    crystalline p k X hprojective a hcard, etale p k X hprojective a hcard ℓ⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.NonemptyDegreeZero.Comparison
