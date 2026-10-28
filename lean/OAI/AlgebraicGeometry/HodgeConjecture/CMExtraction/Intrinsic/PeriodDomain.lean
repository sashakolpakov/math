import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodFamily
import OAI.Geometry.ComplexBall.ArithmeticQuotientBoostBall
import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

/-! # Period Domain -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodDomain.Multiplicity

noncomputable section

/-! The constructed signed period varies continuously over the native
connected ball domain. -/

open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
open scoped Classical _root_.Matrix

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

omit [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E] in
theorem native_domain_eq_ball : P.domain = (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (P.μ P.b) : Set Geometry.ComplexBall.PrescribedSignsB.BallChart) := by
  ext x
  change (Geometry.ComplexBall.PrescribedSignsB.localB P.embeddings (Matrix.diagonal ![1, 1, P.b]) P.distinguished
    (Geometry.ComplexBall.PrescribedSignsB.lineVector x) (star (Geometry.ComplexBall.PrescribedSignsB.lineVector x))).re < 0 ↔
      Complex.normSq (x 0) + Complex.normSq (x 1) < -(P.μ P.b).re
  rw [NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.localB_diagonal_real]
  simp only [Geometry.ComplexBall.PrescribedSignsB.lineVector, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  change Complex.normSq (x 0) + Complex.normSq (x 1) + (P.μ P.b).re * Complex.normSq 1 < 0 ↔ _
  rw [Complex.normSq_one, mul_one]
  constructor <;> intro h <;> linarith

omit [IsGalois ℚ E] in
theorem native_domain_connected (hP : P.IsAdmissible) : IsConnected P.domain := by
  rw [native_domain_eq_ball]
  exact (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ball_pathConnected (P.μ P.b) hP.2.2.2.1).isConnected

def nativeOrigin (hP : P.IsAdmissible) : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain} :=
  ⟨0, by
    rw [native_domain_eq_ball E P]
    change Complex.normSq 0 + Complex.normSq 0 < -(P.μ P.b).re
    simpa only [Complex.normSq_zero, zero_add] using neg_pos.mpr hP.2.2.2.1⟩

variable (hP : P.IsAdmissible) (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (P.imaginaryScalar * Multiplicity.nativeTensorPairing E P v x y))

theorem nativePeriod_continuous :
    Continuous (fun z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain} => RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.ofSiegel (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he z)) := by
  apply Continuous.subtype_mk
  exact (continuousOn_iff_continuous_domRestrict.mp
    (PeriodFamily.Multiplicity.nativePeriodMatrix_differentiable E P hP hμ v hv e he).continuousOn)

theorem nativePeriod_halfDet_continuous (g : ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks (Fin s × Fin 3) ℝ) :
    Continuous (fun z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain} => RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet g (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he z)) :=
  (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDetDomain_continuous g).comp (nativePeriod_continuous E P hP hμ v hv e he)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodDomain.Multiplicity
