import OAI.Analysis.PDE.Schauder.Calculus.Deformation.Operator
import OAI.Analysis.PDE.Schauder.Calculus.Deformation.Periodic
import OAI.Analysis.PDE.Schauder.Calculus.TransformedValue
import OAI.Analysis.PDE.Schauder.Calculus.LatticeJets
import OAI.Analysis.Normed.Operator.ClosedSubspace.CalculusClosedSubspace

open Set Module
open scoped ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ} {α : ℝ} {I : Set ℝ}
  {Φ : ℝ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4}
  {B₀ f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ}
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}

theorem PeriodicDeformationFields.mooreOperator_periodic
    (C : PeriodicDeformationFields r α I Φ B₀ f e b)
    (J : LatticeJetLifts hΩK α e b) (hr : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r) (hα : 0 ≤ α)
    {t : ℝ} (ht : t ∈ I) (v : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b) :
    C.fields.mooreOperator hα J.first J.second (t,v) ∈ OAI.Analysis.Normed.Function.Holder.latticeHolder e b := by
  have hmain : transformedBackgroundMooreField hα (C.fields.background t)
      (C.fields.jacobian t) (C.fields.curvature t) (J.first v) (J.second v) ∈
      OAI.Analysis.Normed.Function.Holder.latticeHolder e b :=
    transformedBackgroundMooreField_periodic e b hr hα _ _ _ _ _
      (C.background_periodic t ht) (C.jacobian_periodic t ht)
      (C.curvature_periodic t ht) (J.first_periodic v) (J.second_periodic v)
  exact (OAI.Analysis.Normed.Function.Holder.latticeHolder e b).sub_mem hmain (C.source_periodic t ht)

def PeriodicDeformationFields.periodicOperator
    (C : PeriodicDeformationFields r α I Φ B₀ f e b)
    (J : LatticeJetLifts hΩK α e b) (hr : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r) (hα : 0 ≤ α)
    (p : ℝ × OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b) :
    OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := {x | r x ≤ 0}) (α := α) e b := by
  classical
  exact if ht : p.1 ∈ I then
    ⟨C.fields.mooreOperator hα J.first J.second p,C.mooreOperator_periodic J hr hα ht p.2⟩
  else 0

theorem PeriodicDeformationFields.coe_periodicOperator
    (C : PeriodicDeformationFields r α I Φ B₀ f e b)
    (J : LatticeJetLifts hΩK α e b) (hr : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r) (hα : 0 ≤ α)
    (p : ℝ × OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b)
    (hp : p.1 ∈ I) :
    (C.periodicOperator J hr hα p).val = C.fields.mooreOperator hα J.first J.second p := by
  simp only [PeriodicDeformationFields.periodicOperator,dite_eq_left hp]

theorem PeriodicDeformationFields.contDiffOn_periodicOperator
    (C : PeriodicDeformationFields r α I Φ B₀ f e b)
    (J : LatticeJetLifts hΩK α e b) (hr : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r) (hα : 0 ≤ α)
    (hI : IsOpen I) :
    ContDiffOn ℝ ∞ (C.periodicOperator J hr hα) {p | p.1 ∈ I} := by
  apply OAI.Analysis.Normed.Operator.ClosedSubspace.contDiffOn_infty_of_isometry
    (OAI.Analysis.Normed.Function.Holder.latticeHolder (K := {x | r x ≤ 0}) (α := α) e b).subtypeₗᵢ
    (hI.preimage continuous_fst)
  exact (C.fields.contDiffOn_mooreOperator hα J.first J.second).congr
    (fun p hp => C.coe_periodicOperator J hr hα p hp)

end OAI.Analysis.PDE.Schauder
