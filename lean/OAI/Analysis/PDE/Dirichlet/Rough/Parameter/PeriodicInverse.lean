import OAI.Analysis.PDE.Dirichlet.Rough.Parameter.CompactDeformation
import OAI.Analysis.PDE.Dirichlet.Rough.Parameter.PeriodizationSmooth

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

namespace ParameterDeformation

open OAI.Analysis.Calculus.SmoothExtension

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
variable {E T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [Nontrivial E] [AddCommGroup T]

/-- Periodizing disjoint compact deformations produces an actual jointly smooth
family of global inverses. This is the geometric, rather than formal, change
of variables used for boundary regularity. -/
theorem exists_smooth_periodic_deformation_inverse
    (L : T →+ E) (hL : ∀ R : ℝ, {z : T | ‖L z‖ ≤ R}.Finite)
    {K : Set E} (hK : IsCompact K)
    (hdis : ∀ x z w, x + L z ∈ K → x + L w ∈ K → z = w)
    (h : Z × E → E) (hh : ContDiff ℝ ∞ h)
    (hs : ∀ t x, x ∉ K → h (t, x) = 0) (hzero : ∀ x, h (0, x) = 0) :
    ∃ d : ℝ, 0 < d ∧
      (∀ t : Z, ‖t‖ < d → Function.Bijective (periodicPerturbation L (fun x ↦ h (t, x)))) ∧
      ContDiffOn ℝ ∞
        (fun p : Z × E ↦ Function.invFun (periodicPerturbation L (fun x ↦ h (p.1, x))) p.2)
        {p | ‖p.1‖ < d} := by
  classical
  obtain ⟨d, hd, hbij, hInv⟩ := ParameterDeformation.exists_smooth_compact_deformation_inverse hh hK hs hzero
  let g : Z × E → E := fun p ↦
    if ‖p.1‖ < d then Function.invFun (fun x ↦ x + h (p.1, x)) p.2 - p.2 else 0
  have hfg (t : Z) (ht : ‖t‖ < d) (x : E) :
      (x + g (t, x)) + h (t, x + g (t, x)) = x := by
    have he := Function.invFun_eq ((hbij t ht).surjective x)
    simpa only [g, ite_eq_left ht, add_sub_cancel] using he
  have hgf (t : Z) (ht : ‖t‖ < d) (x : E) :
      (x + h (t, x)) + g (t, x + h (t, x)) = x := by
    apply (hbij t ht).injective
    exact hfg t ht (x + h (t, x))
  have gs : ∀ t x, x ∉ K → g (t, x) = 0 := by
    intro t x hx
    by_cases ht : ‖t‖ < d
    · have he : x + g (t, x) = x := by
        apply (hbij t ht).injective
        dsimp only
        rw [hfg t ht, hs t x hx, add_zero]
      exact (add_eq_left.mp he)
    · simp [g, ht]
  have hI : IsOpen {t : Z | ‖t‖ < d} := isOpen_lt continuous_norm continuous_const
  have hg : ContDiffOn ℝ ∞ g {p | ‖p.1‖ < d} := by
    apply (hInv.sub contDiffOn_snd).congr
    intro p hp
    change ‖p.1‖ < d at hp
    simp [g, hp]
  have hperbij (t : Z) (ht : ‖t‖ < d) :
      Function.Bijective (periodicPerturbation L (fun x ↦ h (t, x))) :=
    periodicPerturbation_bijective L _ _ (hs t) (gs t) hdis (hgf t ht) (hfg t ht)
  refine ⟨d, hd, hperbij, ?_⟩
  have hpG : ContDiffOn ℝ ∞
      (fun p : Z × E ↦ periodicPerturbation L (fun x ↦ g (p.1, x)) p.2)
      {p | ‖p.1‖ < d} := by
    exact contDiffOn_snd.add (ParameterDeformation.contDiffOn_parametricPeriodization L hL hK g gs hI hg)
  apply hpG.congr
  intro p hp
  apply (hperbij p.1 hp).injective
  rw [Function.invFun_eq ((hperbij p.1 hp).surjective p.2)]
  exact (periodicPerturbation_leftInverse L _ _ (gs p.1) (hs p.1) hdis (hfg p.1 hp) p.2).symm

end ParameterDeformation
end OAI.Analysis.PDE.Dirichlet
