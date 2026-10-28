import OAI.Analysis.PDE.Dirichlet.PositiveOpen
import OAI.Analysis.PDE.Dirichlet.C2HolderImplicit

open Set Filter Module
open scoped Topology Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {Ω K S : Set (CoordinateSpace n 4)} {hΩK : Ω ⊆ K} {α : ℝ}
  {e : CoordinateSpace n 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}

omit [Fintype ι] in
/-- The actual implicit solution map preserves strict Hessian positivity
on a compact fundamental region. Admissibility is proved open here, rather
than being an extra open-set assumption in the continuation argument. -/
theorem periodicMooreDirichlet_positive_continuation
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ closure Ω) (hS : IsCompact S) (hSK : S ⊆ K)
    (hΩper : LatticePeriodic e b (fun x ↦ x ∈ Ω))
    (hKper : LatticePeriodic e b (fun x ↦ x ∈ K))
    (hα : 0 ≤ α) (v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (hv : LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v)))
    (u : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b)
    (hu : ∀ x : S, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.Normed.Function.Holder.HolderMap.value
      (quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots (v + u.val)) ⟨x, hSK x.property⟩)).PosDef)
    (L : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b ≃L[ℝ]
      OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := K) (α := α) e b)
    (hL : fderiv ℝ (periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα OAI.Analysis.Calculus.Quaternion.fourSlots v hv) u =
      L.toContinuousLinearMap) :
    let F := periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα OAI.Analysis.Calculus.Quaternion.fourSlots v hv
    ∀ᶠ g in 𝓝 (F u), ∃ w : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b,
      (∀ x : S, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.Normed.Function.Holder.HolderMap.value
        (quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots (v + w.val)) ⟨x, hSK x.property⟩)).PosDef) ∧
      F w = g := by
  let U : Set (OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b) :=
    {w | ∀ x : S, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.Normed.Function.Holder.HolderMap.value
      (quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots (v + w.val)) ⟨x, hSK x.property⟩)).PosDef}
  have htranslate : Continuous (fun w :
      OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b ↦ v + w.val) :=
    continuous_const.add continuous_subtype_val
  have hopen : IsOpen U := (isOpen_positive_hessian_on_compact
    (hΩK := hΩK) (α := α) hΩ hKΩ hS hSK).preimage htranslate
  exact periodicMooreDirichlet_image_mem_nhds hΩ hKΩ hΩper hKper hα OAI.Analysis.Calculus.Quaternion.fourSlots v hv u L hL
    (hopen.mem_nhds hu)

end OAI.Analysis.PDE.Dirichlet
