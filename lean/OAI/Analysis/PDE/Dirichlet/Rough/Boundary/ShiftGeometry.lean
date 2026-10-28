import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.Shift

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem mapsTo_of_injective_eq_self_off {F : E → E} (hi : Function.Injective F)
    {S : Set E} (hoff : ∀ x ∉ S, F x = x) : MapsTo F S S := by
  intro x hx
  by_contra hn
  have he : F (F x) = F x := hoff (F x) hn
  have hxF : F x = x := hi he
  exact hn (hxF.symm ▸ hx)

theorem cutoffShift_mapsTo {η : E → ℝ} (v : E) (t : ℝ) {S : Set E}
    (hs : Function.support η ⊆ S) (hi : Function.Injective (cutoffShift η v t)) :
    MapsTo (cutoffShift η v t) S S := by
  apply mapsTo_of_injective_eq_self_off hi
  intro x hx
  apply cutoffShift_eq_self
  by_contra hn
  exact hx (hs hn)

/-- Conjugating a cutoff shift inside a chart, with a physical cutoff to
exclude the irrelevant values of the globally extended inverse chart. -/
def chartShiftDisplacement (G P : E → E) (ρ η : E → ℝ) (v : E)
    (t : ℝ) (x : E) : E :=
  ρ x • (G (cutoffShift η v t (P x)) - G (P x))

theorem contDiff_chartShiftDisplacement {G P : E → E} {ρ η : E → ℝ}
    (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P)
    (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η) (v : E) :
    ContDiff ℝ ∞ (fun p : ℝ × E ↦ chartShiftDisplacement G P ρ η v p.1 p.2) := by
  exact (hρ.comp contDiff_snd).smul
    ((hG.comp ((contDiff_cutoffShift hη v).comp
      (contDiff_fst.prodMk (hP.comp contDiff_snd)))).sub (hG.comp (hP.comp contDiff_snd)))

theorem chartShiftDisplacement_zero (G P : E → E) (ρ η : E → ℝ) (v x : E) :
    chartShiftDisplacement G P ρ η v 0 x = 0 := by
  simp [chartShiftDisplacement, cutoffShift_zero]

theorem chartShiftDisplacement_eq_zero (G P : E → E) (ρ η : E → ℝ) (v : E)
    (t : ℝ) {x : E} (hx : ρ x = 0) : chartShiftDisplacement G P ρ η v t x = 0 := by
  simp [chartShiftDisplacement, hx]

theorem chartShiftDisplacement_preserves_level
    (G P : E → E) (ρ η r : E → ℝ) (v : E) (t : ℝ)
    {U W : Set E} (hρ : Function.support ρ ⊆ U) (hη : Function.support η ⊆ W)
    (hP : MapsTo P U W) (hGP : ∀ x ∈ U, G (P x) = x)
    (hplateau : ∀ x ∈ U, η (P x) ≠ 0 → ρ x = 1)
    (hi : Function.Injective (cutoffShift η v t))
    (ℓ : E →L[ℝ] ℝ) (c : ℝ) (hlevel : ∀ z ∈ W, r (G z) = c + ℓ z)
    (hv : ℓ v = 0) (x : E) :
    r (x + chartShiftDisplacement G P ρ η v t x) = r x := by
  by_cases hρx : ρ x = 0
  · simp [chartShiftDisplacement_eq_zero G P ρ η v t hρx]
  by_cases hηx : η (P x) = 0
  · simp [chartShiftDisplacement, cutoffShift_eq_self v t hηx]
  have hx : x ∈ U := hρ hρx
  have hz : P x ∈ W := hP hx
  have hs : cutoffShift η v t (P x) ∈ W := cutoffShift_mapsTo v t hη hi hz
  rw [chartShiftDisplacement, hplateau x hx hηx, one_smul, hGP x hx, add_sub_cancel]
  rw [hlevel _ hs, cutoffShift_preserves_linear η v t ℓ hv]
  rw [← hlevel _ hz, hGP x hx]

end OAI.Analysis.PDE.Dirichlet
