import OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry
import OAI.NumberTheory.PadicHodge.GeometricComparison.WeilRoot
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integrality
import OAI.AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback

/-! # Completion -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The complete repaired Completion proposition as an explicit input, specialized to the actual special fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- Exactly the native geometric Completion proposition; no theorem with a proof gap is imported. -/
def Completion.GeometricWeightInput : Prop :=
  ∀ {k : Type u} [Field k] [Fintype k]
    (q : ℕ) (_hq : Fintype.card k = q)
    (A : Over (Spec (CommRingCat.of k)))
    [GrpObj A] [IsCommMonObj A] [Smooth A.hom] [IsProper A.hom]
    [GeometricallyIntegral A.hom]
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : (ℓ : k) ≠ 0)
    (α : AlgebraicClosure ℚ_[ℓ]),
    (AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.geometricH1Frobenius ℓ k A).HasEigenvalue α →
      IsAlgebraic ℚ α ∧ ∀ z : ℂ,
        Polynomial.aeval z (minpoly ℚ α) = 0 → ‖z‖ = Real.sqrt (q : ℝ)

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.specialFiber_geometricallyIntegral : GeometricallyIntegral A.specialFiber.scheme.hom :=
  Integrality.GeometricIntegrality.of_smooth_geometricallyConnected _

theorem Geometry.AbelianH1Model.specialFiber_eigenvalue_weights (hCompletion : Completion.GeometricWeightInput.{0})
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (α : AlgebraicClosure ℚ_[ℓ])
    (hα : (AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.geometricH1Frobenius ℓ (ZMod q) A.specialFiber.scheme).HasEigenvalue α) :
    IsAlgebraic ℚ α ∧ ∀ z : ℂ,
      Polynomial.aeval z (minpoly ℚ α) = 0 → ‖z‖ = Real.sqrt (q : ℝ) := by
  have hℓ : (ℓ : ZMod q) ≠ 0 := by
    intro hzero
    exact hℓq ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) (Fact.out : ℓ.Prime)).mp
      ((ZMod.natCast_eq_zero_iff ℓ q).mp hzero)).symm
  let : GeometricallyIntegral A.specialFiber.scheme.hom := A.specialFiber_geometricallyIntegral
  exact hCompletion q (by simp) A.specialFiber.scheme ℓ hℓ α hα

/-- Conditional weights for an integral characteristic polynomial of Completion's actual operator.
Agreement with the separately defined IntegralComparison cohomology and operator is a further geometric obligation. -/
theorem Geometry.AbelianH1Model.specialFiber_integral_polynomial_weights (hCompletion : Completion.GeometricWeightInput.{0})
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    [FiniteDimensional (AlgebraicClosure ℚ_[ℓ]) (AlgebraicGeometry.FormalGeometry.Completion.Cohomology.Construction.GeometricH1 ℓ A.specialFiber.scheme)]
    (P : Polynomial ℤ)
    (hP : (AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.geometricH1Frobenius ℓ (ZMod q) A.specialFiber.scheme).charpoly =
      P.map (Int.castRingHom (AlgebraicClosure ℚ_[ℓ])))
    (z : ℂ) (hz : Polynomial.aeval z P = 0) : ‖z‖ = Real.sqrt (q : ℝ) :=
  WeilRoot.WeilRootTransport.integral_complex_roots_of_eigenvalue_bounds (AlgebraicClosure ℚ_[ℓ])
    _ P hP (Real.sqrt (q : ℝ)) (A.specialFiber_eigenvalue_weights hCompletion ℓ hℓq) z hz

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
