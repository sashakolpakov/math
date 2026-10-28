import OAI.Analysis.PDE.Schauder.Dirichlet.CompactSchauderAbsorption
import OAI.Analysis.PDE.Dirichlet.LatticeHolder

open Set Metric Module
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E P V F ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]

omit [NormedSpace ℝ F] in
theorem lattice_norm_le_of_thickened_cell
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} {r : E → ℝ}
    (hr : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (g : E → F) (hg : LatticePeriodic e b g) {M : ℝ}
    (hn : ∀ x, x ∈ cthickening 1 (latticeSublevelCell e b K r) ∩ {x | r x ≤ 0} →
      ‖g x‖ ≤ M) : ∀ x, r x ≤ 0 → ‖g x‖ ≤ M := by
  intro x hx
  let y := latticeRepresentative e b x
  have hy : y ∈ latticeSublevelCell e b K r :=
    latticeRepresentative_mem_sublevelCell e b hr hbounded hx
  have hb : closedBall y 1 ⊆ cthickening 1 (latticeSublevelCell e b K r) :=
    (closedBall_subset_cthickening_singleton _ _).trans
      (cthickening_subset_of_subset 1 (singleton_subset_iff.mpr hy))
  have hys : y ∈ cthickening 1 (latticeSublevelCell e b K r) ∩ {x | r x ≤ 0} :=
    ⟨hb (by simp), hy.2⟩
  have h := hn y hys
  simpa only [y, hg.representative] using h

/-- A Hölder norm on the infinite periodic domain is controlled by a
single thickened fundamental cell. Both points are translated together. -/
theorem lattice_holder_norm_le_of_thickened_cell
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} {r : E → ℝ}
    (hr : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    {α M : ℝ} (hα : 0 ≤ α) (hM : 0 ≤ M)
    (g : E → F) (hg : LatticePeriodic e b g)
    (v : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} F α)
    (hv : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value v x = g x)
    (hn : ∀ x, x ∈ cthickening 1 (latticeSublevelCell e b K r) ∩ {x | r x ≤ 0} →
      ‖g x‖ ≤ M)
    (hh : ∀ x, x ∈ cthickening 1 (latticeSublevelCell e b K r) ∩ {x | r x ≤ 0} →
      ∀ y, y ∈ cthickening 1 (latticeSublevelCell e b K r) ∩ {x | r x ≤ 0} →
        ‖g x-g y‖ ≤ M * dist x y ^ α) :
    ‖v‖ ≤ 3 * M := by
  have hglobal := lattice_norm_le_of_thickened_cell e b hr hbounded g hg hn
  have hholder := lattice_holder_of_thickened_cell e b hr hbounded
    (fun _ : Unit => g) (fun _ => hg) hα hM hM
    (fun _ => hglobal) (fun _ => hh)
  apply OAI.Analysis.Normed.Function.Holder.HolderMap.norm_le_of_bounds hα (by positivity) v
  · intro x
    rw [hv]
    exact (hglobal x x.property).trans (by linarith)
  · intro x y
    rw [hv, hv]
    change ‖g (x : E)-g (y : E)‖ ≤ 3 * M * dist (x : E) (y : E) ^ α
    have h := hholder () x x.property y y.property
    convert h using 1 ; ring

/-- Fixed-cover absorption on a periodic domain. The error is measured in
the actual global Hölder norm, and the compactness is only of a thickened
fundamental cell, not of the full lifted domain. -/
theorem lattice_holder_norm_absorption [ProperSpace E]
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (ρ : ↥(cthickening 1 (latticeSublevelCell e b K r) ∩ {x | r x ≤ 0}) → ℝ)
    (hρ : ∀ x, 0 < ρ x)
    {α : ℝ} (hα : 0 < α) {I : Type*}
    (g : I → E → F) (hg : ∀ i, LatticePeriodic e b (g i))
    (v : I → OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} F α)
    (hv : ∀ i x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (v i) x = g i x)
    (N : I → ℝ) (hN : ∀ i, 0 ≤ N i)
    (hlocal : ∀ ε > 0, ∃ D > 0, ∀ i
      (x y : ↥(cthickening 1 (latticeSublevelCell e b K r) ∩ {x | r x ≤ 0})),
      dist y x ≤ ρ x → ‖g i y‖ ≤ ε * ‖v i‖ + D * N i ∧
      ∀ z : ↥(cthickening 1 (latticeSublevelCell e b K r) ∩ {x | r x ≤ 0}),
        dist z x ≤ ρ x → ‖g i y-g i z‖ ≤
          (ε * ‖v i‖ + D * N i) * dist y z ^ α) :
    ∃ C > 0, ∀ i, ‖v i‖ ≤ C * N i := by
  let S := cthickening 1 (latticeSublevelCell e b K r) ∩ {x | r x ≤ 0}
  have hS : IsCompact S :=
    (isCompact_latticeSublevelCell e b hK hr).cthickening.inter_right
      (isClosed_le hr continuous_const)
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨A, hA, hcover⟩ := OAI.Analysis.PDE.Schauder.compact_fixed_cover_holder_constant (E := F) ρ hρ hα
  obtain ⟨D, hD, hloc⟩ := hlocal (1 / (6*A)) (by positivity)
  refine ⟨6*A*D, by positivity, ?_⟩
  intro i
  have hNi := hN i
  let M := (1 / (6*A)) * ‖v i‖ + D * N i
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨hn, hh⟩ := hcover (fun x : S => g i x) M hM (hloc i)
  have hbound := lattice_holder_norm_le_of_thickened_cell e b hrp hbounded hα.le
    (mul_nonneg hA.le hM) (g i) (hg i) (v i) (hv i)
    (fun x hx => hn ⟨x, hx⟩) (fun x hx y hy => hh ⟨x, hx⟩ ⟨y, hy⟩)
  have heq : 3 * (A * M) = ‖v i‖ / 2 + 3*A*D*N i := by
    dsimp [M]
    field_simp
    ; ring
  rw [heq] at hbound
  nlinarith only [hbound]

end OAI.Analysis.PDE.Dirichlet
