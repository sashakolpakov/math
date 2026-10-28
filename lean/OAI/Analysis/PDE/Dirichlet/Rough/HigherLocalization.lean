import OAI.Analysis.Calculus.FiniteExtension.Halfspace.Extension.Ball
import OAI.Analysis.PDE.Dirichlet.Rough.MixedTangentJets

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace OAI.Analysis.PDE.Dirichlet

variable {m N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

/-- The finite extension may be recentered at every boundary point.
This is used locally in an induction on one fixed working domain. -/
theorem exists_contDiff_extension_halfball_at
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1)
    {a : E} (ha : ℓ a = 0) {R : ℝ} (hR : 0 < R) (f : E → ℝ)
    (hf : ContDiffOn ℝ N f ({x | 0 ≤ ℓ x} ∩ ball a R)) :
    ∃ g : E → ℝ, ContDiff ℝ N g ∧
      EqOn g f ({x | 0 ≤ ℓ x} ∩ closedBall a (R/2)) := by
  have hs : ContDiffOn ℝ N (fun z : E ↦ f (a+z)) ({x | 0 ≤ ℓ x} ∩ ball 0 R) := by
    apply hf.comp (contDiff_const.add contDiff_id).contDiffOn
    intro z hz
    constructor
    · simpa only [Set.mem_ofPred_eq, map_add, ha, zero_add, id_eq] using hz.1
    · simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero, id_eq] using hz.2
  obtain ⟨g,hg,he⟩ := OAI.Analysis.Calculus.FiniteExtension.exists_contDiff_extension_halfball ℓ ν hν hR _ hs
  refine ⟨fun x ↦ g (x-a), hg.comp (contDiff_id.sub contDiff_const), ?_⟩
  intro x hx
  have hsub : x-a ∈ {z | 0 ≤ ℓ z} ∩ closedBall 0 (R/2) := by
    constructor
    · simpa only [Set.mem_ofPred_eq, map_sub, ha, sub_zero] using hx.1
    · simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hx.2
  change g (x-a) = f x
  rw [he hsub]
  simp only [← add_sub_assoc, add_sub_cancel_left]

/-- Agreement on a relative half-ball implies equality of all tangent
parameter derivatives, without requiring arbitrary outside extensions to
agree. Tangent translations stay on the same side of the boundary. -/
theorem tangent_parameter_tensors_congr
    (ℓ : E →L[ℝ] ℝ) {a : E} {R : ℝ} {f g : E → ℝ}
    (he : EqOn g f ({x | 0 ≤ ℓ x} ∩ ball a R))
    {x : E} (hx : x ∈ {x | 0 ≤ ℓ x} ∩ ball a R)
    (N : ℕ) (v : Fin N → ℓ.ker) :
    iteratedFDeriv ℝ N (fun t : ℓ.ker ↦ g (x+(t:E))) 0 v =
      iteratedFDeriv ℝ N (fun t : ℓ.ker ↦ f (x+(t:E))) 0 v := by
  have hgerm : (fun t : ℓ.ker ↦ g (x+(t:E))) =ᶠ[𝓝 0]
      (fun t : ℓ.ker ↦ f (x+(t:E))) := by
    have hc : Continuous (fun t : ℓ.ker ↦ x+(t:E)) :=
      continuous_const.add continuous_subtype_val
    have hb : ∀ᶠ t : ℓ.ker in 𝓝 0, x+(t:E) ∈ ball a R := by
      apply hc.continuousAt.eventually_mem
      simpa only [ZeroMemClass.coe_zero, add_zero] using isOpen_ball.mem_nhds hx.2
    filter_upwards [hb] with t ht
    apply he
    refine ⟨?_,ht⟩
    change 0 ≤ ℓ (x+(t:E))
    rw [map_add, show ℓ (t:E) = 0 from t.property, add_zero]
    exact hx.1
  exact congrArg
    (fun B : ContinuousMultilinearMap ℝ (fun _ : Fin N ↦ ℓ.ker) ℝ ↦ B v)
    ((hgerm.iteratedFDeriv ℝ N).eq_of_nhds)

end OAI.Analysis.PDE.Dirichlet
