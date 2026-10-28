import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicCoefficientHodge
import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicCoefficientRealization

/-! # Intrinsic Coefficient Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicCoefficientComparison

noncomputable section

/-! The exact coefficient equations describe the Hodge structure whose
realization is the original polarized abelian variety. -/

theorem nativeCoefficientHodgeStructure_holomorphic
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {g N s : ℕ} {δ : Fin g → ℕ}
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (ξ : E) (hξ : ξ ≠ 0)
    (e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (hline : AbelianModuli.ReferenceFamily.Normalized.HodgeLine.NativeHermitianMarking.nativeNormalizedHodgeLine A ρ s hs hg hdegree (P.embeddings P.distinguished) e =
      Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z})
    (hrank : ∀ i : Fin s, AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A.abelian ρ
      ((P.embeddings i).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) (P.firstLieRank i))
    (x : ComplexMultiplication.WeightOne.CM.Complexification (Fin 3 → E)) :
    x ∈ (IntrinsicCoefficientRealization.nativeCoefficientHodgeStructure A ρ s hs hg hdegree).holomorphic ↔
      ClosedCoefficientPeriods.componentPrescribed P (AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ)
        (e (Geometry.ComplexBall.PrescribedSignsB.lineVector z)) (PeriodCoordinates.cmPeriodCoordinates P hP x) := by
  let c := IntrinsicCoefficientCoordinates.nativeRationalCoefficientCoordinates A ρ s hs hg hdegree
  obtain ⟨u, rfl⟩ := (c.baseChange ℚ ℂ _ _).surjective x
  rw [show (c.baseChange ℚ ℂ _ _) u ∈
      (IntrinsicCoefficientRealization.nativeCoefficientHodgeStructure A ρ s hs hg hdegree).holomorphic ↔
      u ∈ (AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A))).holomorphic
    from (AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A))).transport_holomorphic c u]
  rw [IntrinsicCoefficientHodge.native_period_holomorphic_iff_component P hP A ρ hs hg hdegree hρ ξ hξ e z hline hrank]
  rw [show PeriodCoordinates.cmPeriodCoordinates P hP ((c.baseChange ℚ ℂ _ _) u) = _ from
    IntrinsicCoefficientCoordinates.nativeCoefficientCoordinates_pair A ρ s hs hg hdegree P hP u]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicCoefficientComparison
