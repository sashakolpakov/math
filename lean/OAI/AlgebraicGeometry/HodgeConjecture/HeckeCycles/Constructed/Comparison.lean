import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoherentCrystallineComparison
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AbelianProjectivePresentation

/-! # Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Comparison.CM

noncomputable section

/-! The full GeometricComparison comparison and ordinary polynomial use a constructed
projective presentation of the actual Albanese. An auxiliary prime
different from q is chosen internally. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)
  (κ : K →+* AlgebraicClosure ℚ) (jComplex : AlgebraicClosure ℚ →+* ℂ)
  (iota : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
  {H : Type} [CommRing H] [Algebra ℚ H] (ρ : A.HeckeRealization H)

def Conclusion (h : Fin 3 → H) : Prop :=
    ∃ hD : FiniteDimensional ℚ_[q] A.DeRham,
    ∃ hC : FiniteDimensional ℚ_[q] A.Crystalline,
    ∃ hB : FiniteDimensional ℂ (A.ComplexBetti (jComplex.comp κ)),
      letI := hD
      letI := hC
      letI := hB
      ∃ (cmp : A.Crystalline ≃ₗ[ℚ_[q]] A.DeRham)
        (φ : A.Crystalline ≃ₗ[ℚ_[q]] A.Crystalline)
        (Fil : NumberTheory.PadicHodge.GeometricComparison.Linear.FiniteFiltration ℚ_[q] A.DeRham),
        φ.toLinearMap = A.crystallineFrobenius ∧ Fil.step = A.Fil ∧
        let φdR := cmp.symm.trans (φ.trans cmp)
        (∀ h k, Commute (A.deRhamHecke ρ h) (A.deRhamHecke ρ k)) ∧
        (∀ h, Commute φdR.toLinearMap (A.deRhamHecke ρ h)) ∧
        Ordinary.Polynomial.CM.heckePolynomialValue q φdR.toLinearMap
          (fun i => A.deRhamHecke ρ (h i)) = 0 ∧
        NumberTheory.PadicHodge.ExtremeSlopesNewtonSummands.CM.Adapter.VerifiedNativePurityComparison A κ jComplex iota H ρ (AbelianProjectivePresentation.CM.presentation A (jComplex.comp κ)) Fil φdR

theorem polynomial_and_purity
    (hGeometricComparison : NumberTheory.PadicHodge.GeometricComparisonAdapter.CM.ExtremeSlopes.GeometricComparisonInput)
    (hplace : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = iota.comp κ)
    (h : Fin 3 → H)
    (hp : Ordinary.Polynomial.CM.heckePolynomialValue q
      (FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius (ZMod q) A.specialFiber.scheme)
      (fun i => Specialized.CM.Hecke.specializedHeckeAction A ρ (h i)) = 0) :
    Conclusion A κ jComplex iota ρ h := by
  let ℓ : ℕ := if q = 2 then 3 else 2
  have hprime : ℓ.Prime := by
    dsimp only [ℓ]
    split <;> decide
  let : Fact ℓ.Prime := ⟨hprime⟩
  have hℓq : ℓ ≠ q := by
    dsimp only [ℓ]
    split <;> omega
  exact CoherentCrystallineComparison.CM.polynomial_and_purity_from_full_GeometricComparison
    A κ jComplex iota ρ (AbelianProjectivePresentation.CM.presentation A (jComplex.comp κ))
    hGeometricComparison hplace ℓ hℓq h hp

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Comparison.CM
