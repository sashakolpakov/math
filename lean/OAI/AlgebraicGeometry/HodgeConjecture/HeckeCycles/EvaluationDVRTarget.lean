import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluatedTargetBaseChange
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationDVRMap
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedEvaluation

/-! # Evaluation DVR Target -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationDVRTarget.CM

noncomputable section

/-! Base change of actual evaluated targets to another evaluation DVR.
Both the fraction-field map and the residue square are derived from the
field embedding, so the same original special target is recovered. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedEvaluation.Lifts

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  {R F L L' : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F]
  [Field L] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
  [Field L'] [Algebra F L'] [Algebra R L'] [IsScalarTower R F L']
  (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR R L) (V' : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR R L') (σ : L →ₐ[F] L')
  (b : B.R →+* R)

local notation "φ" => AlgHom.toRingHom (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationDVRMap.CM.map V V' σ)

theorem base_eq : (φ).comp ((algebraMap R V.carrier).comp b) = (algebraMap R V'.carrier).comp b :=
  RingHom.ext (fun a => (EvaluationDVRMap.CM.map V V' σ).commutes (b a))

theorem fraction_square : (algebraMap V'.carrier L').comp φ =
    σ.toRingHom.comp (algebraMap V.carrier L) :=
  RingHom.ext (EvaluationDVRMap.CM.map_fraction V V' σ)

variable (z : Isogenies.NeighborCounting.Evaluated.Targets.Lifts.EvaluatedTarget D V.carrier L ((algebraMap R V.carrier).comp b))

def target : Isogenies.NeighborCounting.Evaluated.Targets.Lifts.EvaluatedTarget D V'.carrier L' ((algebraMap R V'.carrier).comp b) :=
  EvaluatedTargetBaseChange.CM.changeBase
    (EvaluatedTargetBaseChange.CM.target (L' := L') z φ) (base_eq V V' σ b)

theorem target_map : (target V V' σ b z).map = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ z.map :=
  (EvaluatedTargetBaseChange.CM.changeBase_map _ (base_eq V V' σ b)).trans
    (EvaluatedTargetBaseChange.CM.target_map z φ σ.toRingHom (fraction_square V V' σ))

variable (ρ : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R)
  (hbase : Isogenies.NeighborCounting.Lifts.ResidueCompatible D R b ρ)

theorem residue_square (r : V.carrier) :
    (ρ.trans V'.residueIso).symm (IsLocalRing.residue V'.carrier (φ r)) =
      (ρ.trans V.residueIso).symm (IsLocalRing.residue V.carrier r) :=
  congrArg ρ.symm (EvaluationDVRMap.CM.geometric_residue V V' σ r)

theorem specialPoint_eq :
    (target V V' σ b z).specialPoint (Isogenies.NeighborCounting.ConstructedEvaluation.Lifts.evaluation_residueCompatible V' hbase) =
      z.specialPoint (Isogenies.NeighborCounting.ConstructedEvaluation.Lifts.evaluation_residueCompatible V hbase) := by
  have hgeneric := EvaluatedTargetBaseChange.CM.residueCompatible φ
    (ρ.trans V.residueIso) (ρ.trans V'.residueIso) (residue_square V V' σ ρ)
    (Isogenies.NeighborCounting.ConstructedEvaluation.Lifts.evaluation_residueCompatible V hbase)
  exact (EvaluatedTargetBaseChange.CM.changeBase_specialPoint _ (base_eq V V' σ b)
    (ρ.trans V'.residueIso) hgeneric (Isogenies.NeighborCounting.ConstructedEvaluation.Lifts.evaluation_residueCompatible V' hbase)).trans
      (EvaluatedTargetBaseChange.CM.specialPoint_eq z φ
        (ρ.trans V.residueIso) (ρ.trans V'.residueIso) (residue_square V V' σ ρ)
        (Isogenies.NeighborCounting.ConstructedEvaluation.Lifts.evaluation_residueCompatible V hbase) hgeneric)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationDVRTarget.CM
