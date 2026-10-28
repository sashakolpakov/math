import OAI.MeasureTheory.Kakeya.Hausdorff
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

open OAI.Analysis.Fourier.Wave

open Set _root_.MeasureTheory Metric
open scoped Topology

noncomputable section
namespace OAI.Geometry.Kakeya.Quadratic

/-- A fixed positive length of segments in any open patch of directions
already forces full dimension under the genuine linear Kakeya theorem. -/
theorem dimH_eq_of_open_directions (hK : OAI.MeasureTheory.Kakeya.KakeyaConjecture)
    {n : ℕ} (hn : 2 ≤ n) {K U : Set (Space n)} (hU : IsOpen U)
    {v : Space n} (hv : ‖v‖ = 1) (hvU : v ∈ U) {τ : ℝ} (hτ : 0 < τ)
    (hseg : ∀ ω ∈ U, ‖ω‖ = 1 → ∃ x : Space n,
      ∀ t ∈ Icc (-τ) τ, x + t • ω ∈ K) :
    dimH K = n := by
  classical
  let S := Metric.sphere (0 : Space n) 1
  let R (w : S) : Space n ≃ₗᵢ[ℝ] Space n :=
    (ℝ ∙ ((w : Space n)-v)).orthogonal.reflection
  have hw (w : S) : ‖(w : Space n)‖ = 1 := by simp [S]
  have hRv (w : S) : R w w = v := Submodule.reflection_sub ((hw w).trans hv.symm)
  let O (w : S) : Set (Space n) := R w ⁻¹' U
  have hO (w : S) : IsOpen (O w) := hU.preimage (R w).continuous
  have hcover : S ⊆ ⋃ w : S, O w := by
    intro w hwS
    refine mem_iUnion.mpr ⟨⟨w, hwS⟩, ?_⟩
    change R ⟨w, hwS⟩ w ∈ U
    rwa [hRv]
  obtain ⟨F, hF⟩ := (isCompact_sphere (0 : Space n) 1).elim_finite_subcover O hO hcover
  let f (w : S) (z : Space n) := (2*τ)⁻¹ • (R w).symm z
  let L : Set (Space n) := ⋃ w ∈ F, f w '' K
  have hLK : OAI.MeasureTheory.Kakeya.IsKakeyaSet L := by
    intro ω hω
    have hωS : ω ∈ S := by simpa [S, mem_sphere, dist_zero_right] using hω
    obtain ⟨w, hwF, hwO⟩ := mem_iUnion₂.mp (hF hωS)
    obtain ⟨x, hx⟩ := hseg (R w ω) hwO (by simpa using hω)
    refine ⟨f w x, ?_⟩
    rintro z ⟨t, ht, rfl⟩
    have htτ : 2*τ*t ∈ Icc (-τ) τ := by constructor <;> nlinarith [ht.1, ht.2]
    apply mem_iUnion₂.mpr
    refine ⟨w, hwF, x+(2*τ*t) • R w ω, hx _ htτ, ?_⟩
    dsimp [f]
    rw [map_add, map_smul, LinearIsometryEquiv.symm_apply_apply, smul_add, smul_smul]
    congr 1
    field_simp
  have hdim : dimH L ≤ dimH K := by
    change dimH (⋃ w ∈ (F : Set S), f w '' K) ≤ dimH K
    rw [dimH_bUnion F.finite_toSet.countable]
    apply iSup₂_le
    intro w hwF
    have hf : Differentiable ℝ (f w) := by dsimp [f]; fun_prop
    exact hf.differentiableOn.dimH_image_le
  apply le_antisymm
  · calc
      dimH K ≤ dimH (univ : Set (Space n)) := dimH_mono (subset_univ _)
      _ = n := by rw [Real.dimH_univ_eq_finrank]; simp [Space]
  · simpa [hK n hn L hLK] using hdim

end OAI.Geometry.Kakeya.Quadratic
