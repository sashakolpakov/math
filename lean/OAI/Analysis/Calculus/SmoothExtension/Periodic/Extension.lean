import OAI.Analysis.Calculus.SmoothExtension.Periodic.Extension.Average
import OAI.Analysis.Calculus.SmoothExtension.Periodic.Extension.Compact

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.Calculus.SmoothExtension

variable {E T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [AddCommGroup T]

/-- A closed periodic set with a compact set of representatives admits a
globally periodic C^q extension of every compatible family of local C^q
extensions. All gluing and periodization are constructed in the proof. -/
theorem exists_periodic_contDiff_extension_of_local
    (L : T →+ E) (hL : ∀R : ℝ, {z : T | ‖L z‖ ≤ R}.Finite)
    {K C : Set E} (hK : IsClosed K) (hC : IsCompact C)
    (hKper : ∀x ∈ K, ∀z, x + L z ∈ K)
    (hcover : ∀x ∈ K, ∃z, x + L z ∈ C)
    (q : ℕ) (u : E → ℝ) (huper : ∀x ∈ K, ∀z, u (x + L z) = u x)
    (hl : ∀x ∈ K, ∃U : Set E, IsOpen U ∧ x ∈ U ∧
      ∃g : E → ℝ, ContDiff ℝ q g ∧ ∀y ∈ K ∩ U, g y = u y) :
    ∃g : E → ℝ, ContDiff ℝ q g ∧
      (∀x z, g (x + L z) = g x) ∧ ∀x ∈ K, g x = u x := by
  obtain ⟨g,hg,hgu⟩ := exists_contDiff_extension_of_local hK q u hl
  obtain ⟨ρ,hρ,hρc,hρ0,hρ1⟩ := exists_smooth_compact_one_on_compact hC
  apply exists_periodic_extension_of_weight L hL hKper u g ρ huper hg hgu
    (hρ.of_le (by simp)) hρc hρ0
  intro x hx
  obtain ⟨z,hz⟩ := hcover x hx
  exact ⟨z,hρ1 _ hz⟩

theorem exists_periodic_contDiff_extension_of_local_on
    (L : T →+ E) (hL : ∀R : ℝ, {z : T | ‖L z‖ ≤ R}.Finite)
    {K C : Set E} (hK : IsClosed K) (hC : IsCompact C)
    (hKper : ∀x ∈ K, ∀z, x + L z ∈ K)
    (hcover : ∀x ∈ K, ∃z, x + L z ∈ C)
    (q : ℕ) (u : E → ℝ) (huper : ∀x ∈ K, ∀z, u (x + L z) = u x)
    (hl : ∀x ∈ K, ∃U : Set E, IsOpen U ∧ x ∈ U ∧
      ∃g : E → ℝ, ContDiffOn ℝ q g U ∧ ∀y ∈ K ∩ U, g y = u y) :
    ∃g : E → ℝ, ContDiff ℝ q g ∧
      (∀x z, g (x + L z) = g x) ∧ ∀x ∈ K, g x = u x := by
  obtain ⟨g,hg,hgu⟩ := exists_contDiff_extension_of_local_on hK q u hl
  obtain ⟨ρ,hρ,hρc,hρ0,hρ1⟩ := exists_smooth_compact_one_on_compact hC
  apply exists_periodic_extension_of_weight L hL hKper u g ρ huper hg hgu
    (hρ.of_le (by simp)) hρc hρ0
  intro x hx
  obtain ⟨z,hz⟩ := hcover x hx
  exact ⟨z,hρ1 _ hz⟩

end OAI.Analysis.Calculus.SmoothExtension
