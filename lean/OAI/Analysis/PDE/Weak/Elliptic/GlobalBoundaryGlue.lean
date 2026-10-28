import OAI.Analysis.PDE.Weak.Elliptic.Classical.Glue
import OAI.Analysis.Calculus.SmoothExtension.Periodic.Extension

open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational OAI.Analysis.Calculus.SmoothExtension

variable {m : ℕ}

def closedDirichletValue (Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (v : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) :
    OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ := Ω.indicator v

theorem closedDirichletValue_local_representatives
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω) {q : ℕ}
    (w v : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hv : ContDiffOn ℝ q v Ω)
    (hvw : ∀ᵐx, x ∈ Ω → v x = w x)
    (hbd : ∀x ∈ closure Ω \ Ω, ∃U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m), IsOpen U ∧ x ∈ U ∧
      ∃g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ, ContDiffOn ℝ q g U ∧
        (∀ᵐy, y ∈ Ω ∩ U → g y = w y) ∧ (∀y ∈ (closure Ω \ Ω) ∩ U, g y = 0)) :
    ∀x ∈ closure Ω, ∃U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m), IsOpen U ∧ x ∈ U ∧
      ∃g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ, ContDiffOn ℝ q g U ∧
        ∀y ∈ closure Ω ∩ U, g y = closedDirichletValue Ω v y := by
  intro x hx
  by_cases hxin : x ∈ Ω
  · refine ⟨Ω,hΩ,hxin,v,hv,?_⟩
    intro y hy
    simp [closedDirichletValue,hy.2]
  · obtain ⟨U,hU,hxU,g,hg,hgw,hgz⟩ := hbd x ⟨hx,hxin⟩
    have heq : EqOn g v (Ω ∩ U) := by
      apply continuous_eqOn_of_local_ae (hΩ.inter hU)
        (hg.continuousOn.mono inter_subset_right) (hv.continuousOn.mono inter_subset_left)
      filter_upwards [hvw,hgw] with y hyv hyg
      intro hy
      exact (hyg hy).trans (hyv hy.1).symm
    refine ⟨U,hU,hxU,g,hg,?_⟩
    intro y hy
    by_cases hyin : y ∈ Ω
    · simpa [closedDirichletValue,hyin] using heq ⟨hyin,hy.2⟩
    · simp [closedDirichletValue,hyin,hgz y ⟨⟨hy.1,hyin⟩,hy.2⟩]

theorem add_mem_of_backward_invariant {T : Type*} [AddCommGroup T]
    (L : T →+ OAI.Analysis.PDE.Variational.CellCoordinates m) {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)}
    (hΩ : ∀z x, x + L z ∈ Ω → x ∈ Ω) :
    ∀z x, x ∈ Ω → x + L z ∈ Ω := by
  intro z x hx
  apply hΩ (-z) (x + L z)
  simpa only [map_neg,add_neg_cancel_right] using hx

theorem closure_add_mem_of_invariant {T : Type*} [AddCommGroup T]
    (L : T →+ OAI.Analysis.PDE.Variational.CellCoordinates m) {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)}
    (hΩ : ∀z x, x ∈ Ω → x + L z ∈ Ω) :
    ∀x ∈ closure Ω, ∀z, x + L z ∈ closure Ω := by
  intro x hx z
  have hs : Ω ⊆ (fun y ↦ y + L z) ⁻¹' closure Ω :=
    fun y hy ↦ subset_closure (hΩ z y hy)
  exact closure_minimal hs (isClosed_closure.preimage (continuous_id.add_const _)) hx

theorem closedDirichletValue_periodic {T : Type*} [AddCommGroup T]
    (L : T →+ OAI.Analysis.PDE.Variational.CellCoordinates m) {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)}
    (hΩ : ∀z x, x + L z ∈ Ω → x ∈ Ω)
    {v : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ} (hv : ∀z x, x ∈ Ω → v (x + L z) = v x) :
    ∀x z, closedDirichletValue Ω v (x + L z) = closedDirichletValue Ω v x := by
  intro x z
  by_cases hx : x ∈ Ω
  · simp [closedDirichletValue,hx,add_mem_of_backward_invariant L hΩ z x hx,hv z x hx]
  · have hz : x + L z ∉ Ω := fun h ↦ hx (hΩ z x h)
    simp [closedDirichletValue,hx,hz]

/-- Honest local-to-global boundary regularity. Boundary representatives
are explicit inputs here; no trace or regularity theorem is assumed inside
the statement. Their almost-everywhere identities are upgraded on overlaps. -/
theorem global_periodic_dirichlet_representative
    {T : Type*} [AddCommGroup T] (L : T →+ OAI.Analysis.PDE.Variational.CellCoordinates m)
    (hL : ∀R : ℝ, {z : T | ‖L z‖ ≤ R}.Finite)
    {Ω C : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω) (hC : IsCompact C)
    (hΩper : ∀z x, x + L z ∈ Ω → x ∈ Ω)
    (hcover : ∀x ∈ closure Ω, ∃z, x + L z ∈ C)
    (q : ℕ) (w v : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hv : ContDiffOn ℝ q v Ω)
    (hvw : ∀ᵐx, x ∈ Ω → v x = w x)
    (hvper : ∀z x, x ∈ Ω → v (x + L z) = v x)
    (hbd : ∀x ∈ closure Ω \ Ω, ∃U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m), IsOpen U ∧ x ∈ U ∧
      ∃g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ, ContDiffOn ℝ q g U ∧
        (∀ᵐy, y ∈ Ω ∩ U → g y = w y) ∧ (∀y ∈ (closure Ω \ Ω) ∩ U, g y = 0)) :
    ∃f : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ, ContDiff ℝ q f ∧ (∀x z, f (x + L z) = f x) ∧
      EqOn f v Ω ∧ (∀x ∈ closure Ω \ Ω, f x = 0) ∧
      (∀ᵐx, x ∈ Ω → f x = w x) := by
  obtain ⟨f,hf,hfp,hfe⟩ := OAI.Analysis.Calculus.SmoothExtension.exists_periodic_contDiff_extension_of_local_on L hL
    isClosed_closure hC (closure_add_mem_of_invariant L (add_mem_of_backward_invariant L hΩper))
    hcover q (closedDirichletValue Ω v)
    (fun x _ z ↦ closedDirichletValue_periodic L hΩper hvper x z)
    (closedDirichletValue_local_representatives hΩ w v hv hvw hbd)
  have he : EqOn f v Ω := fun x hx ↦ by
    simpa [closedDirichletValue,hx] using hfe x (subset_closure hx)
  refine ⟨f,hf,hfp,he,?_,?_⟩
  · intro x hx
    simpa [closedDirichletValue,hx.2] using hfe x hx.1
  · filter_upwards [hvw] with x hx
    intro hxin
    exact (he hxin).trans (hx hxin)

end OAI.Analysis.PDE.Weak
