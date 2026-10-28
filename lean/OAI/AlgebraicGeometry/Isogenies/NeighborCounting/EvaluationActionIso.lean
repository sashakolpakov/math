import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedEvaluation
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointDataSpecialization

/-! # Evaluation Action Iso -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! The evaluated integral lift is the actual base change of the
original source, retaining the full polarization, action and marking. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.GeometricPoint} (l : Lifts.IntegralLift D R b residueIso x) (v : EvaluationDVRLifts.EvaluationDVR R L)

def Lifts.IntegralLift.evaluationActionIso : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso
    (l.actionData.pullback (Spec.map (CommRingCat.ofHom (algebraMap R v.carrier))))
    (l.overEvaluationDVR v).actionData :=
  PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso.pullbackComp D.integral.universal.data l.map
    (Spec.map (CommRingCat.ofHom (algebraMap R v.carrier)))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
