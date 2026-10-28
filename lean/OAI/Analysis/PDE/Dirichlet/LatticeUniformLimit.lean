import OAI.Analysis.PDE.Dirichlet.LatticeCauchy

open Set Module Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

theorem latticePeriodic_bcf_of_eq {E P V F ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]
    {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P} {S : Set E}
    (hS : LatticePeriodic e lat (fun x ↦ x ∈ S)) (u : S →ᵇ F) (f : E → F)
    (hf : LatticePeriodic e lat f) (hu : ∀ x : S, u x = f x) :
    LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension u) := by
  intro x l
  let y := e.symm ((e x).1 + (l : P), (e x).2)
  have hy : y ∈ S ↔ x ∈ S := Iff.of_eq (hS x l)
  by_cases hx : x ∈ S
  · change OAI.Analysis.Normed.Function.Holder.boundedZeroExtension u y = OAI.Analysis.Normed.Function.Holder.boundedZeroExtension u x
    rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ (hy.mpr hx), OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ hx, hu, hu]
    exact hf x l
  · have hy' : y ∉ S := fun h ↦ hx (hy.mp h)
    change OAI.Analysis.Normed.Function.Holder.boundedZeroExtension u y = OAI.Analysis.Normed.Function.Holder.boundedZeroExtension u x
    simp only [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension, zeroExtend, dite_eq_right hx, dite_eq_right hy']

/-- A uniform limit of the original periodic fields on one closed cell
makes their full-domain bounded-continuous representatives Cauchy. -/
theorem cauchySeq_bcf_of_lattice_uniform_limit {E P V F ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} {r : E → ℝ}
    (hr : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (u : ℕ → ({x | r x ≤ 0} →ᵇ F)) (f : ℕ → E → F)
    (hf : ∀ n, LatticePeriodic e lat (f n))
    (hu : ∀ n (x : {x | r x ≤ 0}), u n x = f n x)
    (v : latticeSublevelCell e lat K r → F)
    (hlim : TendstoUniformly (fun n (x : latticeSublevelCell e lat K r) ↦ f n x) v atTop) :
    CauchySeq u := by
  apply cauchySeq_bcf_of_lattice_cell e lat hr hbounded u
    (fun n ↦ latticePeriodic_bcf_of_eq (hr.comp (fun t ↦ t ≤ 0)) (u n) (f n) (hf n) (hu n))
  have hl : TendstoUniformly
      (fun n (x : latticeSublevelCell e lat K r) ↦ OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (u n) x) v atTop := by
    convert hlim using 1
    funext n x
    rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ x.property.2, hu]
  exact (uniform_limit_zeroExtend hl).uniformCauchySeqOn

end OAI.Analysis.PDE.Dirichlet
