import OAI.Analysis.PDE.Dirichlet.PositiveContinuation
import OAI.Analysis.PDE.Dirichlet.C2HolderQuaternionPeriodicity

open Set Filter Module
open scoped Topology Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {Ω : Set (CoordinateSpace n 4)} {r : CoordinateSpace n 4 → ℝ}
  {hΩK : Ω ⊆ {x | r x ≤ 0}} {α : ℝ}
  {e : CoordinateSpace n 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P} {C : Set V}

/-- Positivity on the compact lattice cell is equivalent to positivity
on the entire closed periodic domain, including its physical boundary. -/
theorem positive_hessian_iff_latticeCell
    (hΩ : IsOpen Ω) (hKΩ : {x | r x ≤ 0} ⊆ closure Ω)
    (hΩper : LatticePeriodic e b (fun x ↦ x ∈ Ω))
    (hrper : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (f : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (hf : LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value f))) :
    (∀ x : {x | r x ≤ 0},
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots f) x)).PosDef) ↔
    (∀ x : latticeSublevelCell e b C r,
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots f)
        ⟨x, x.property.2⟩)).PosDef) := by
  constructor
  · exact fun h x ↦ h ⟨x, x.property.2⟩
  · intro h x
    let y := latticeRepresentative e b x
    have hy : y ∈ latticeSublevelCell e b C r :=
      latticeRepresentative_mem_sublevelCell e b hrper hbounded x.property
    have heq := (quaternionHessianField_latticePeriodic hΩ hKΩ hΩper
      (hrper.comp (fun t ↦ t ≤ 0)) OAI.Analysis.Calculus.Quaternion.fourSlots f hf).representative x
    change OAI.Analysis.Normed.Function.Holder.boundedZeroExtension _ y =
      OAI.Analysis.Normed.Function.Holder.boundedZeroExtension _ (x : CoordinateSpace n 4) at heq
    rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ hy.2, OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ x.property] at heq
    rw [← heq]
    exact h ⟨y, hy⟩

/-- Actual local solvability preserves admissibility on the whole periodic
closed domain. The compactness used in the openness argument is supplied by
the geometric fundamental cell, not by a fictitious compact full domain. -/
theorem periodicMooreDirichlet_positive_lattice_continuation
    (hΩ : IsOpen Ω) (hKΩ : {x | r x ≤ 0} ⊆ closure Ω)
    (hΩper : LatticePeriodic e b (fun x ↦ x ∈ Ω))
    (hr : Continuous r) (hrper : LatticePeriodic e b r)
    (hC : IsCompact C) (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hα : 0 ≤ α) (v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (hv : LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v)))
    (u : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b)
    (hu : ∀ x : {x | r x ≤ 0}, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.Normed.Function.Holder.HolderMap.value
      (quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots (v + u.val)) x)).PosDef)
    (L : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b ≃L[ℝ]
      OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := {x | r x ≤ 0}) (α := α) e b)
    (hL : fderiv ℝ (periodicMooreDirichletOperator hΩ hKΩ hΩper
      (hrper.comp (fun t ↦ t ≤ 0)) hα OAI.Analysis.Calculus.Quaternion.fourSlots v hv) u = L.toContinuousLinearMap) :
    let F := periodicMooreDirichletOperator hΩ hKΩ hΩper
      (hrper.comp (fun t ↦ t ≤ 0)) hα OAI.Analysis.Calculus.Quaternion.fourSlots v hv
    ∀ᶠ g in 𝓝 (F u), ∃ w : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b,
      (∀ x : {x | r x ≤ 0}, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.Normed.Function.Holder.HolderMap.value
        (quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots (v + w.val)) x)).PosDef) ∧ F w = g := by
  have he := periodicMooreDirichlet_positive_continuation hΩ hKΩ
    (isCompact_latticeSublevelCell e b hC hr) inter_subset_right hΩper
    (hrper.comp (fun t ↦ t ≤ 0)) hα v hv u (fun x ↦ hu ⟨x, x.property.2⟩) L hL
  filter_upwards [he] with g hg
  obtain ⟨w, hw, hFw⟩ := hg
  refine ⟨w, ?_, hFw⟩
  apply (positive_hessian_iff_latticeCell hΩ hKΩ hΩper hrper hbounded (v + w.val) ?_).mpr hw
  change LatticePeriodic e b
    (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v + OAI.Analysis.Normed.Function.Holder.C2Holder.value w.val))
  rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_add]
  exact hv.add w.property.2

end OAI.Analysis.PDE.Dirichlet
