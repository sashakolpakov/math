import OAI.Analysis.Calculus.SmoothExtension.Periodic.Extension.Sublevel
import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.C2Representative

noncomputable section
open Set Filter Module
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Interior pointwise regularity and actual boundary patch extensions glue
to a genuine periodic global representative on the closed physical domain. -/
theorem exists_periodic_representative_of_local_regularities
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {C : Set V} (hC : IsCompact C)
    {r : E → ℝ} (hr : Continuous r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    {q : ℕ} (f : E → ℝ) (hfp : LatticePeriodic e b f)
    (hint : ∀ x, r x < 0 → ContDiffAt ℝ q f x)
    (hbd : ∀ a, r a = 0 → ∃ O : Set E, IsOpen O ∧ a ∈ O ∧
      ∃ g : E → ℝ, ContDiffOn ℝ q g O ∧ ∀ x ∈ O, r x ≤ 0 → g x = f x) :
    ∃ g : E → ℝ, ContDiff ℝ q g ∧ LatticePeriodic e b g ∧
      ∀ x, r x ≤ 0 → g x = f x := by
  apply OAI.Analysis.Calculus.SmoothExtension.exists_latticePeriodic_contDiff_sublevel_extension_on
    e b hC hr hrp hbounded q f hfp
  intro x hx
  by_cases hi : r x < 0
  · refine ⟨{x | r x < 0},isOpen_lt hr continuous_const,hi,f,?_,?_⟩
    · intro y hy
      exact (hint y hy).contDiffWithinAt
    · intro y hy hyr
      rfl
  · exact hbd x (le_antisymm hx (le_of_not_gt hi))

section Jets
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance roughGlobalFirstGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance roughGlobalFirstSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance roughGlobalSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance roughGlobalSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

omit [FiniteDimensional ℝ E] in
/-- Replacing a global C² function by a more regular representative on a
closed domain preserves both actual derivative fields, including boundary
points, whenever the interior is dense in that domain. -/
theorem first_second_eqOn_of_eqOn_dense_interior
    {Ω D : Set E} (hΩ : IsOpen Ω) (hΩD : Ω ⊆ D) (hDΩ : D ⊆ closure Ω)
    {f g : E → F} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (he : EqOn f g D) :
    EqOn (fderiv ℝ f) (fderiv ℝ g) D ∧
      EqOn (fderiv ℝ (fderiv ℝ f)) (fderiv ℝ (fderiv ℝ g)) D := by
  have hlocal (x : E) (hx : x ∈ Ω) : f =ᶠ[𝓝 x] g := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact he (hΩD hy)
  have hfirst : EqOn (fderiv ℝ f) (fderiv ℝ g) Ω := fun x hx ↦ (hlocal x hx).fderiv_eq
  have hsecond : EqOn (fderiv ℝ (fderiv ℝ f)) (fderiv ℝ (fderiv ℝ g)) Ω :=
    fun x hx ↦ (hlocal x hx).fderiv.fderiv_eq
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hg1 : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have hf2 : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ f)) := hf1.fderiv_right (by norm_num)
  have hg2 : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ g)) := hg1.fderiv_right (by norm_num)
  exact ⟨hfirst.of_subset_closure hf1.continuous.continuousOn hg1.continuous.continuousOn hΩD hDΩ,
    hsecond.of_subset_closure hf2.continuous.continuousOn hg2.continuous.continuousOn hΩD hDΩ⟩

end Jets
end OAI.Analysis.PDE.Dirichlet
