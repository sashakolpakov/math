import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Lagrangians
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELDatum
import OAI.NumberTheory.ArithmeticGroups.CongruenceLevelTrace
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion

/-! # Reference Datum -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ReferenceDatum.CM

noncomputable section

/-! The actual admissible arithmetic reference datum. The full PrescribedSigns and
Riemann projectivity prerequisites are discharged by native proofs. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]

theorem nativePrescribedSignsInput (Place : Type) [Fintype Place] :
    NumberTheory.ArithmeticGroups.CongruenceLevelDatum.PrescribedSignsInput K Place := by
  have hWeakApproximation : Geometry.ComplexBall.PrescribedSignsB.WeakApproximationInput K := by
    intro ι hι v hn hd
    exact NumberTheory.Approximation.Weak.HodgeWeakApproximation.weak_approximation K v hn hd
  exact Geometry.ComplexBall.PrescribedSignsB.lagrangians_with_prescribed_compact_place_signs hWeakApproximation

theorem nativeRiemannInput : NumberTheory.ArithmeticGroups.CongruenceLevelDatum.RiemannInput := by
  intro T _ _ _ Γ _ _
  exact Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.riemann_projectivity_criterion T Γ

theorem nativeCongruenceLevelInput (s : ℕ) : HeckeCycles.ReferenceDatum.CM.CongruenceLevelInput K s :=
  NumberTheory.ArithmeticGroups.CongruenceLevelTrace.reference_polarized_abelian_moduli_datum
    (nativePrescribedSignsInput K (Fin s)) nativeRiemannInput

theorem exists_admissible_reference_datum (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (dref : Fin places.count → Bool) :
    ∃ P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum K places.count,
      P.IsAdmissible ∧ P.b = B.b ∧ P.embeddings = HeckeCycles.ReferenceDatum.CM.embeddings K places ∧
        P.distinguished = places.distinguished ∧ P.compactSigns = dref :=
  HeckeCycles.PELDatum.CM.admissible_reference_datum K B places (nativeCongruenceLevelInput K places.count) dref

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ReferenceDatum.CM
