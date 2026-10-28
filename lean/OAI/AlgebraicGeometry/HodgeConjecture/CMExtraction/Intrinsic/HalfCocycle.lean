import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.UnitaryPeriod
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HolomorphicFrameRoot

/-! # Half Cocycle -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.HalfCocycle

noncomputable section

/-! The determinant square-root cocycle of the actual signed native
period. The frame root supplies the change of trivialization, while the
projective denominator supplies the line-annihilator half determinant. -/

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HolomorphicFrameRoot.Multiplicity
open scoped Classical _root_.Matrix

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq PeriodAction.Multiplicity.nativeDomainAction

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

def nativeProjectiveFactor (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) : ℂ :=
  RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator (ArchFrame.archUnitaryBlock E P P.distinguished g) z

theorem nativeProjectiveFactor_ne_zero (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) : nativeProjectiveFactor E P g z ≠ 0 :=
  ArchFrame.native_arch_denominator_ne_zero E P g z z.property

theorem nativeProjectiveFactor_continuous (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) :
    Continuous (nativeProjectiveFactor E P g) := by
  have hl : Continuous (fun z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain} =>
      RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector z.val) := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain} => z.val 0)
      exact (continuous_apply 0).comp continuous_subtype_val
    · change Continuous (fun z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain} => z.val 1)
      exact (continuous_apply 1).comp continuous_subtype_val
    · exact continuous_const
  unfold nativeProjectiveFactor RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator
  fun_prop

theorem nativeProjectiveFactor_one (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    nativeProjectiveFactor E P 1 z = 1 := by
  simp [nativeProjectiveFactor]

theorem nativeProjectiveFactor_mul (g h : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    nativeProjectiveFactor E P (g * h) z =
      nativeProjectiveFactor E P g (h • z) * nativeProjectiveFactor E P h z := by
  unfold nativeProjectiveFactor
  rw [map_mul]
  have hp := RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator_mul
    (ArchFrame.archUnitaryBlock E P P.distinguished g) (ArchFrame.archUnitaryBlock E P P.distinguished h) z.val
    (ArchFrame.native_arch_denominator_ne_zero E P h z z.property)
  rw [ArchFrame.native_chartImage_eq_periodMap E P h z z.property] at hp
  exact hp

variable [IsGalois ℚ E] (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (P.imaginaryScalar * Multiplicity.nativeTensorPairing E P v x y))

def nativeHalfFactor (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) : ℂ :=
  nativeProjectiveFactor E P g z * FrameRoot.Multiplicity.nativeFrameRoot E P hP hμ v hv e he (g • z) /
    FrameRoot.Multiplicity.nativeFrameRoot E P hP hμ v hv e he z

theorem nativeHalfFactor_continuous (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) :
    Continuous (nativeHalfFactor E P hP hμ v hv e he g) :=
  ((nativeProjectiveFactor_continuous E P g).mul
    ((FrameRoot.Multiplicity.nativeFrameRoot E P hP hμ v hv e he).continuous.comp (PeriodAction.Multiplicity.nativeDomain_smul_continuous E P g))).div
      (FrameRoot.Multiplicity.nativeFrameRoot E P hP hμ v hv e he).continuous (FrameRoot.Multiplicity.nativeFrameRoot_ne_zero E P hP hμ v hv e he)

theorem nativeHalfFactor_sq (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    nativeHalfFactor E P hP hμ v hv e he g z ^ 2 =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.denominatorDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E P e v he g))
        (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.ofSiegel (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he z)) := by
  rw [UnitaryPeriod.nativePeriod_unitary_denominator E P hP hμ v hv e he g z]
  unfold nativeHalfFactor
  rw [div_pow, mul_pow, FrameRoot.Multiplicity.nativeFrameRoot_sq, FrameRoot.Multiplicity.nativeFrameRoot_sq]
  congr 1
  exact mul_comm _ _

theorem nativeHalfFactor_one (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    nativeHalfFactor E P hP hμ v hv e he 1 z = 1 := by
  rw [nativeHalfFactor, nativeProjectiveFactor_one, one_smul, one_mul]
  exact div_self (FrameRoot.Multiplicity.nativeFrameRoot_ne_zero E P hP hμ v hv e he z)

theorem nativeHalfFactor_mul (g h : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    nativeHalfFactor E P hP hμ v hv e he (g * h) z =
      nativeHalfFactor E P hP hμ v hv e he g (h • z) * nativeHalfFactor E P hP hμ v hv e he h z := by
  have hz := FrameRoot.Multiplicity.nativeFrameRoot_ne_zero E P hP hμ v hv e he z
  have hh := FrameRoot.Multiplicity.nativeFrameRoot_ne_zero E P hP hμ v hv e he (h • z)
  unfold nativeHalfFactor
  rw [nativeProjectiveFactor_mul, mul_smul g h z]
  field_simp

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.HalfCocycle
