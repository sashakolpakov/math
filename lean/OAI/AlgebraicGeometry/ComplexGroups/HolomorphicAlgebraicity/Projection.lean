import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! # Projection -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone

noncomputable section

/-!
# Proper linear projections of closed complex cones

If the kernel of a linear projection meets a closed complex cone only at the
origin, the projection controls the norm on the cone. Consequently the
restricted projection is proper. These are the compactness estimates needed
to construct equations by finite projection.
-/

open Set _root_.Metric
open scoped _root_.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F]

local instance : ProperSpace E := FiniteDimensional.proper ℂ E

/-- A projection with no nonzero kernel point on a closed cone controls the
norm everywhere on the cone. -/
theorem norm_le_projection {S : Set E}
    (hS : IsClosed S)
    (hcone : ∀ (c : ℂ) ⦃x : E⦄, x ∈ S → c • x ∈ S)
    (L : E →L[ℂ] F)
    (hker : ∀ x ∈ S, L x = 0 → x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ S, ‖x‖ ≤ C * ‖L x‖ := by
  let K : Set E := sphere 0 1 ∩ S
  have hK : IsCompact K := (isCompact_sphere _ _).inter_right hS
  have hnonzero (x : E) (hx : x ∈ K) : ‖L x‖ ≠ 0 := by
    intro hz
    have hx0 := hker x hx.2 (norm_eq_zero.mp hz)
    have hnorm : ‖x‖ = 1 := by
      simpa only [mem_sphere_iff_norm, sub_zero] using hx.1
    simp [hx0] at hnorm
  have hcont : ContinuousOn (fun x => (‖L x‖)⁻¹) K :=
    L.continuous.norm.continuousOn.inv₀ hnonzero
  obtain ⟨C, hC, hbound⟩ := (hK.image_of_continuousOn hcont).isBounded.exists_pos_norm_le
  refine ⟨C, hC, fun x hx => ?_⟩
  by_cases hx0 : x = 0
  · simp [hx0]
  · let c : ℂ := ‖x‖
    have hc : c ≠ 0 := by
      dsimp [c]
      exact_mod_cast (norm_ne_zero_iff.mpr hx0)
    have hcnorm : ‖c‖ = ‖x‖ := by simp [c]
    let y : E := c⁻¹ • x
    have hynorm : ‖y‖ = 1 := by
      rw [show y = c⁻¹ • x from rfl, norm_smul, norm_inv, hcnorm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)
    have hy : y ∈ K := ⟨by
      simpa only [mem_sphere_iff_norm, sub_zero] using hynorm,
      hcone c⁻¹ hx⟩
    have hnormpos : 0 < ‖L y‖ := lt_of_le_of_ne (norm_nonneg _) (hnonzero y hy).symm
    have hCy : (‖L y‖)⁻¹ ≤ C := by
      simpa only [norm_inv, Real.norm_of_nonneg (norm_nonneg _)] using
        hbound _ (mem_image_of_mem _ hy)
    have hone : 1 ≤ C * ‖L y‖ := (inv_le_iff_one_le_mul₀ hnormpos).mp hCy
    have hcy : c • y = x := by
      rw [show y = c⁻¹ • x from rfl, smul_smul, mul_inv_cancel₀ hc, one_smul]
    calc
      ‖x‖ = ‖x‖ * 1 := (mul_one _).symm
      _ ≤ ‖x‖ * (C * ‖L y‖) := mul_le_mul_of_nonneg_left hone (norm_nonneg _)
      _ = C * ‖L x‖ := by
        conv_rhs => rw [← hcy, map_smul, norm_smul, hcnorm]
        ring

/-- Compact subsets of the base have compact inverse images on the cone. -/
theorem isCompact_projection_preimage {S : Set E}
    (hS : IsClosed S)
    (hcone : ∀ (c : ℂ) ⦃x : E⦄, x ∈ S → c • x ∈ S)
    (L : E →L[ℂ] F)
    (hker : ∀ x ∈ S, L x = 0 → x = 0)
    {K : Set F} (hK : IsCompact K) :
    IsCompact (S ∩ L ⁻¹' K) := by
  obtain ⟨C, hC, hbound⟩ := norm_le_projection hS hcone L hker
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  apply isCompact_iff_isClosed_bounded.mpr
  refine ⟨hS.inter (hK.isClosed.preimage L.continuous), ?_⟩
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C * R, fun x hx => ?_⟩
  exact (hbound x hx.1).trans (mul_le_mul_of_nonneg_left (hR _ hx.2) hC.le)

/-- The linear projection restricted to a closed cone is proper when its
kernel meets the cone only at the origin. -/
theorem isProperMap_projection {S : Set E}
    (hS : IsClosed S)
    (hcone : ∀ (c : ℂ) ⦃x : E⦄, x ∈ S → c • x ∈ S)
    (L : E →L[ℂ] F)
    (hker : ∀ x ∈ S, L x = 0 → x = 0) :
    IsProperMap (fun x : S => L x) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨L.continuous.comp continuous_subtype_val, fun K hK => ?_⟩
  rw [Subtype.isCompact_iff]
  convert isCompact_projection_preimage hS hcone L hker hK using 1
  ext x
  simp only [mem_image, mem_preimage, mem_inter_iff, Subtype.exists,
    exists_and_right, exists_eq_right, exists_prop]

/-- Apply the projection estimate to the actual affine cone of a closed
projective set. -/
theorem norm_le_projectiveCone_projection {n k : ℕ}
    {Z : Set (Projectivization ℂ (Fin n → ℂ))} (hZ : IsClosed Z)
    (L : (Fin n → ℂ) →L[ℂ] (Fin k → ℂ))
    (hker : ∀ x ∈ ProjectiveCone.Constructions.Cone.projectiveCone Z, L x = 0 → x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ ProjectiveCone.Constructions.Cone.projectiveCone Z, ‖x‖ ≤ C * ‖L x‖ :=
  norm_le_projection (ProjectiveCone.Constructions.Cone.isClosed_projectiveCone Z hZ) (ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone Z) L hker

/-- The linear projection which drops the first coordinate. -/
def tailProjection (n : ℕ) : (Fin (n + 1) → ℂ) →L[ℂ] (Fin n → ℂ) where
  toFun := Fin.tail
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_pi (fun i => continuous_apply i.succ)

@[simp]
theorem tailProjection_cons {n : ℕ} (c : ℂ) (x : Fin n → ℂ) :
    tailProjection n (Fin.cons c x) = x := rfl

/-- Avoiding one projective center gives the required kernel condition. -/
theorem tailProjection_kernel_trivial {n : ℕ} {S : Set (Fin (n + 1) → ℂ)}
    (hcone : ∀ (c : ℂ) ⦃x : Fin (n + 1) → ℂ⦄, x ∈ S → c • x ∈ S)
    (haxis : (Fin.cons 1 0 : Fin (n + 1) → ℂ) ∉ S) :
    ∀ x ∈ S, tailProjection n x = 0 → x = 0 := by
  intro x hx htail
  have heq : x = (x 0) • (Fin.cons 1 0 : Fin (n + 1) → ℂ) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · change x j.succ = x 0 * 0
      rw [mul_zero]
      exact congrFun htail j
  by_cases hx0 : x 0 = 0
  · simpa only [hx0, zero_smul] using heq
  · apply False.elim
    apply haxis
    have hs := hcone (x 0)⁻¹ hx
    have heq' : (x 0)⁻¹ • x = (Fin.cons 1 0 : Fin (n + 1) → ℂ) := by
      calc
        _ = (x 0)⁻¹ • ((x 0) • (Fin.cons 1 0 : Fin (n + 1) → ℂ)) :=
          congrArg (fun z => (x 0)⁻¹ • z) heq
        _ = _ := by rw [smul_smul, inv_mul_cancel₀ hx0, one_smul]
    rwa [heq'] at hs

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone
