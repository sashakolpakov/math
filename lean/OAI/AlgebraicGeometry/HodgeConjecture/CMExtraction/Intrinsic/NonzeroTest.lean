import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SparseFirst
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaSpanning

/-! # Nonzero Test -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.NonzeroTest.Multiplicity

/-! Choose a genuinely nonzero native theta input together with its
integral finite support and translation level before selecting a prime. -/

open scoped Classical _root_.Matrix

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (P.imaginaryScalar * Multiplicity.nativeTensorPairing E P v x y))

theorem nativeCotangentTheta_sparse_test (z : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) (hz : z ∈ P.domain)
    (η : RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent) :
    ∃ φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3), φ ∈ SparseFirst.nativeSparseInputs ∧
      CotangentTheta.Multiplicity.nativeCotangentThetaOneForm E P hP hμ v hv e he φ z = η := by
  obtain ⟨l, hl⟩ := ThetaSpanning.Multiplicity.nativeCotangentProjection_surjective E P hP hμ v hv e he z hz η
  obtain ⟨φ, hφ, hfirst⟩ := SparseFirst.exists_nativeSparseInput_first
    (ThetaCoordinates.Multiplicity.nativeThetaPeriod E P hP hμ v hv e he z) l
  exact ⟨φ, hφ, (congrArg (CotangentTheta.Multiplicity.nativeCotangentProjection E P hP hμ v hv e he z) hfirst).trans hl⟩

theorem exists_native_nonzero_test_with_level (z : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) (hz : z ∈ P.domain) :
    ∃ φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3),
      (∀ x, x ∉ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors → φ.val x = 0) ∧
      ∃ N : ℕ, ∃ hN : 0 < N,
        (∀ u ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (N : ℚ) (by exact_mod_cast hN.ne'), ∀ x, φ.val (u + x) = φ.val x) ∧
        CotangentTheta.Multiplicity.nativeCotangentThetaOneForm E P hP hμ v hv e he φ z (Pi.single 0 1) = 1 := by
  obtain ⟨φ, hφ, hvalue⟩ := nativeCotangentTheta_sparse_test E P hP hμ v hv e he z hz
    (ContinuousLinearMap.proj (0 : Fin 2))
  obtain ⟨hsupport, N, hN, hperiod⟩ := SparseFirst.nativeSparseInput_level φ hφ
  exact ⟨φ, hsupport, N, hN, hperiod,
    (congrArg (fun l : RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent => l (Pi.single 0 1)) hvalue).trans (by simp)⟩

end AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.NonzeroTest.Multiplicity

namespace AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.NonzeroTest

/-! Retain one genuine integral native theta test and its integer level
as data depending only on the fixed archimedean and rational coordinates. -/

open scoped Classical _root_.Matrix

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (P.imaginaryScalar * Multiplicity.nativeTensorPairing E P v x y))

structure NativeThetaTest where
  test : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3)
  support : ∀ x, x ∉ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors → test.val x = 0
  level : ℕ
  level_pos : 0 < level
  period : ∀ w ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteLattice (level : ℚ) (by exact_mod_cast level_pos.ne'),
    ∀ x, test.val (w + x) = test.val x
  value : CotangentTheta.Multiplicity.nativeCotangentThetaOneForm E P hP hμ v hv e he test
    (PeriodDomain.Multiplicity.nativeOrigin E P hP).val (Pi.single 0 1) = 1

theorem exists_nativeThetaTest : Nonempty (NativeThetaTest E P hP hμ v hv e he) := by
  obtain ⟨φ, hsupport, N, hN, hperiod, hvalue⟩ := Multiplicity.exists_native_nonzero_test_with_level
    E P hP hμ v hv e he (PeriodDomain.Multiplicity.nativeOrigin E P hP).val (PeriodDomain.Multiplicity.nativeOrigin E P hP).property
  exact ⟨⟨φ, hsupport, N, hN, hperiod, hvalue⟩⟩

def nativeThetaTest : NativeThetaTest E P hP hμ v hv e he :=
  Classical.choice (exists_nativeThetaTest E P hP hμ v hv e he)

theorem nativeThetaTest_ne_zero (T : NativeThetaTest E P hP hμ v hv e he) : T.test ≠ 0 := by
  intro h
  have hv := T.value
  rw [h, map_zero] at hv
  simp at hv

end AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.NonzeroTest

end

end OAI
