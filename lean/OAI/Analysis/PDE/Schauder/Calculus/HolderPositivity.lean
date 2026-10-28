import OAI.Analysis.PDE.Dirichlet.PositiveOpen
import OAI.Analysis.PDE.Dirichlet.Periodic.Representatives
import OAI.Analysis.PDE.Schauder.Calculus.HolderPeriodicity

open Set Metric Filter Module
open scoped Topology Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {n : ℕ} {Z P V ι : Type*} [TopologicalSpace Z]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ} {α : ℝ}

theorem isOpen_unit_positive_holder_on_compact
    {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)} (hS : IsCompact S) (hSD : S ⊆ {x | r x ≤ 0}) :
    IsOpen {A : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (Matrix (Fin n) (Fin n) (Quaternion ℝ)) α |
      ∀ x : S, ∀ z ∈ sphere (0 : Fin n → Quaternion ℝ) 1,
        0 < (OAI.Analysis.PDE.Dirichlet.quaternionForm (OAI.Analysis.Normed.Function.Holder.HolderMap.value A ⟨x,hSD x.property⟩) z).re} := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let : CompactSpace (sphere (0 : Fin n → Quaternion ℝ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let q : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (Matrix (Fin n) (Fin n) (Quaternion ℝ)) α →
      (S × sphere (0 : Fin n → Quaternion ℝ) 1) → ℝ :=
    fun A p => (OAI.Analysis.PDE.Dirichlet.quaternionForm (OAI.Analysis.Normed.Function.Holder.HolderMap.value A ⟨p.1,hSD p.1.property⟩) p.2).re
  have hq : Continuous (fun p :
      OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (Matrix (Fin n) (Fin n) (Quaternion ℝ)) α ×
        (S × sphere (0 : Fin n → Quaternion ℝ) 1) => q p.1 p.2) := by
    apply OAI.Analysis.PDE.Dirichlet.continuous_quaternionForm_re
    · exact continuous_eval.comp
        ((OAI.Analysis.Normed.Function.Holder.HolderMap.valueCLM.continuous.comp continuous_fst).prodMk (by fun_prop))
    · fun_prop
  have he : {A : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (Matrix (Fin n) (Fin n) (Quaternion ℝ)) α |
      ∀ x : S, ∀ z ∈ sphere (0 : Fin n → Quaternion ℝ) 1,
        0 < (OAI.Analysis.PDE.Dirichlet.quaternionForm (OAI.Analysis.Normed.Function.Holder.HolderMap.value A ⟨x,hSD x.property⟩) z).re} =
      {A | ∀ p, 0 < q A p} := by
    ext A
    exact ⟨fun h p => h p.1 p.2 p.2.property,fun h x z hz => h (x,⟨z,hz⟩)⟩
  rw [he]
  exact OAI.Analysis.PDE.Dirichlet.isOpen_positive_compact_family q hq

theorem eventually_unit_positive_periodic_holder
    (e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K) (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (A : Z → OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (Matrix (Fin n) (Fin n) (Quaternion ℝ)) α)
    {p₀ : Z} (hA : ContinuousAt A p₀)
    (hper : ∀ᶠ p in 𝓝 p₀, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A p))))
    (hpos : ∀ x : {x | r x ≤ 0}, ∀ z ∈ sphere (0 : Fin n → Quaternion ℝ) 1,
      0 < (OAI.Analysis.PDE.Dirichlet.quaternionForm (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A p₀) x) z).re) :
    ∀ᶠ p in 𝓝 p₀, ∀ x : {x | r x ≤ 0}, ∀ z ∈ sphere (0 : Fin n → Quaternion ℝ) 1,
      0 < (OAI.Analysis.PDE.Dirichlet.quaternionForm (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A p) x) z).re := by
  have ho := isOpen_unit_positive_holder_on_compact
    (α := α) (OAI.Analysis.PDE.Dirichlet.isCompact_latticeSublevelCell e b hK hr) inter_subset_right
  have hn := hA.tendsto (ho.mem_nhds (fun x => hpos ⟨x,x.property.2⟩))
  filter_upwards [hn,hper] with p hp hpp x z hz
  let y := OAI.Analysis.PDE.Dirichlet.latticeRepresentative e b x
  have hy : y ∈ OAI.Analysis.PDE.Dirichlet.latticeSublevelCell e b K r :=
    OAI.Analysis.PDE.Dirichlet.latticeRepresentative_mem_sublevelCell e b hrp hbounded x.property
  have he := hpp.representative x
  change OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A p)) y =
    OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A p)) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) at he
  rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ hy.2,OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ x.property] at he
  rw [← he]
  exact hp ⟨y,hy⟩ z hz

end OAI.Analysis.PDE.Schauder
