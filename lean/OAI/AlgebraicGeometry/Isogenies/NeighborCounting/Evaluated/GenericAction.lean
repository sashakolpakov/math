import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointDataSpecialization
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison

/-! # Generic Action -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated

noncomputable section

/-! The independent proper target model has exactly the original
evaluated generic action datum. The comparison includes the positive
polarization, normalized Poincare bundle and ordered full marking. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
variable {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
variable {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]
variable {b : B.R →+* R} (z : Targets.Lifts.EvaluatedTarget D R L b)

def Targets.Lifts.EvaluatedTarget.genericActionIso : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso
    (z.actionData.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (D.integral.universal.data.pullback z.map) := by
  have e := PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso.pullbackComp D.integral.universal.data z.extension
    (Spec.map (CommRingCat.ofHom (algebraMap R L)))
  rw [z.extension_generic] at e
  exact e

def Targets.Lifts.EvaluatedTarget.genericFamilyIso : AbelianScheme.TateComparison.PELModuli.PELFamilyIso
    ((ActionFamilyComparison.Family.actionFamily z.actionData).pullback (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (ActionFamilyComparison.Family.actionFamily (D.integral.universal.data.pullback z.map)) :=
  (ActionFamilyComparison.Family.actionFamilyPullbackIso z.actionData _).trans (ActionFamilyComparison.Family.actionIsoToFamilyIso z.genericActionIso)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated
