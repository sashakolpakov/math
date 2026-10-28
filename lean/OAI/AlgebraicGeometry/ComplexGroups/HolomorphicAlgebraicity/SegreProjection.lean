import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Projection
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AnalyticFibers

/-! # Segre Projection -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreProjection.Constructions.Segre

noncomputable section

/-!
# Explicit projection centers outside the Segre image

All Segre vectors satisfy the two-by-two minor equations. A diagonal vector
with two nonzero entries violates one minor and therefore avoids every graph
embedded through Segre.
-/

open Set Filter _root_.Metric
open scoped _root_.Topology

variable {ι κ : Type*}

def minor (a₀ a₁ : ι) (b₀ b₁ : κ) (v : ι × κ → ℂ) : ℂ :=
  v (a₀, b₀) * v (a₁, b₁) - v (a₀, b₁) * v (a₁, b₀)

theorem minor_outer (a₀ a₁ : ι) (b₀ b₁ : κ) (v : ι → ℂ) (w : κ → ℂ) :
    minor a₀ a₁ b₀ b₁ (SegreAt.Constructions.Segre.outer v w) = 0 := by
  dsimp [minor, SegreAt.Constructions.Segre.outer]
  ring

theorem minor_smul (a₀ a₁ : ι) (b₀ b₁ : κ) (c : ℂ) (v : ι × κ → ℂ) :
    minor a₀ a₁ b₀ b₁ (c • v) = c ^ 2 * minor a₀ a₁ b₀ b₁ v := by
  simp only [minor, Pi.smul_apply, smul_eq_mul]
  ring

theorem minor_eq_zero_of_mem_segreCone (a₀ a₁ : ι) (b₀ b₁ : κ) (v : ι × κ → ℂ)
    (hv : v ∈ ProjectiveCone.Constructions.Cone.projectiveCone
      (Set.range (fun pq : Projectivization ℂ (ι → ℂ) × Projectivization ℂ (κ → ℂ) =>
        SegreAt.Constructions.Segre.segre pq.1 pq.2))) :
    minor a₀ a₁ b₀ b₁ v = 0 := by
  by_cases hv0 : v = 0
  · simp [hv0, minor]
  obtain ⟨⟨p, q⟩, heq⟩ := hv hv0
  change Projectivization.mk ℂ (SegreAt.Constructions.Segre.outer p.rep q.rep)
    (SegreAt.Constructions.Segre.outer_ne_zero p.rep_nonzero q.rep_nonzero) = Projectivization.mk ℂ v hv0 at heq
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ v (SegreAt.Constructions.Segre.outer p.rep q.rep)
    hv0 (SegreAt.Constructions.Segre.outer_ne_zero p.rep_nonzero q.rep_nonzero)).mp heq.symm
  rw [← hc, minor_smul, minor_outer, mul_zero]

def rankTwoCenter (a₀ a₁ : ι) (b₀ b₁ : κ) : ι × κ → ℂ := by
  classical
  exact Pi.single (a₀, b₀) 1 + Pi.single (a₁, b₁) 1

theorem minor_rankTwoCenter (a₀ a₁ : ι) (b₀ b₁ : κ) (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁) :
    minor a₀ a₁ b₀ b₁ (rankTwoCenter a₀ a₁ b₀ b₁) = 1 := by
  classical
  simp [minor, rankTwoCenter, ha, ha.symm, hb, hb.symm]

theorem rankTwoCenter_not_mem_segreCone (a₀ a₁ : ι) (b₀ b₁ : κ)
    (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁) :
    rankTwoCenter a₀ a₁ b₀ b₁ ∉ ProjectiveCone.Constructions.Cone.projectiveCone
      (Set.range (fun pq : Projectivization ℂ (ι → ℂ) × Projectivization ℂ (κ → ℂ) =>
        SegreAt.Constructions.Segre.segre pq.1 pq.2)) := by
  intro h
  have hz := minor_eq_zero_of_mem_segreCone a₀ a₁ b₀ b₁ _ h
  rw [minor_rankTwoCenter a₀ a₁ b₀ b₁ ha hb] at hz
  exact one_ne_zero hz

section Projection

variable [Fintype ι]
attribute [local instance] Classical.propDecidable

/-- Subtract the distinguished coordinate times the center, then omit that
coordinate. When the center has distinguished coordinate one, its span is
exactly the kernel. -/
def projectionAlong (i : ι) (w : ι → ℂ) :
    (ι → ℂ) →L[ℂ] ({j : ι // j ≠ i} → ℂ) where
  toFun v j := v j - v i * w j
  map_add' u v := by ext j; simp; ring
  map_smul' c v := by ext j; simp [mul_sub]; ring
  cont := continuous_pi fun j => (continuous_apply j.val).sub
    ((continuous_apply i).mul continuous_const)

omit [Fintype ι] in
theorem projectionAlong_kernel (i : ι) (w : ι → ℂ) (hw : w i = 1)
    (v : ι → ℂ) (hv : projectionAlong i w v = 0) : v = (v i) • w := by
  ext a
  by_cases ha : a = i
  · simp [ha, hw]
  · have h := congrFun hv ⟨a, ha⟩
    change v a - v i * w a = 0 at h
    exact sub_eq_zero.mp h

omit [Fintype ι] in
theorem projectionAlong_kernel_trivial {S : Set (ι → ℂ)}
    (hcone : ∀ (c : ℂ) ⦃v : ι → ℂ⦄, v ∈ S → c • v ∈ S)
    (i : ι) (w : ι → ℂ) (hw : w i = 1) (hwS : w ∉ S) :
    ∀ v ∈ S, projectionAlong i w v = 0 → v = 0 := by
  intro v hv hL
  have heq := projectionAlong_kernel i w hw v hL
  by_cases hi : v i = 0
  · simpa only [hi, zero_smul] using heq
  · have hwv : (v i)⁻¹ • v = w := by
      calc
        _ = (v i)⁻¹ • ((v i) • w) := congrArg (fun z : ι → ℂ => (v i)⁻¹ • z) heq
        _ = w := by rw [smul_smul, inv_mul_cancel₀ hi, one_smul]
    exact False.elim (hwS (hwv ▸ hcone (v i)⁻¹ hv))

theorem isProperMap_projectionAlong {S : Set (ι → ℂ)} (hS : IsClosed S)
    (hcone : ∀ (c : ℂ) ⦃v : ι → ℂ⦄, v ∈ S → c • v ∈ S)
    (i : ι) (w : ι → ℂ) (hw : w i = 1) (hwS : w ∉ S) :
    IsProperMap (fun v : S => projectionAlong i w v) :=
  HolomorphicAlgebraicity.Projection.Constructions.Cone.isProperMap_projection hS hcone (projectionAlong i w)
    (projectionAlong_kernel_trivial hcone i w hw hwS)

omit [Fintype ι] in
theorem projectionAlong_self (i : ι) (w : ι → ℂ) (hw : w i = 1) :
    projectionAlong i w w = 0 := by
  ext j
  simp [projectionAlong, hw]

theorem finite_line_intersection {S : Set (ι → ℂ)} (hS : IsClosed S)
    (hcone : ∀ (c : ℂ) ⦃v : ι → ℂ⦄, v ∈ S → c • v ∈ S)
    (i : ι) (w : ι → ℂ) (hw : w i = 1) (hwS : w ∉ S)
    (hlocal : ∀ v ∈ S, v ≠ 0 → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S v)
    (v₀ : ι → ℂ) (hv₀ : projectionAlong i w v₀ ≠ 0) :
    {c : ℂ | v₀ + c • w ∈ S}.Finite := by
  let L := projectionAlong i w
  let line : ℂ → (ι → ℂ) := fun c => v₀ + c • w
  have hline : Differentiable ℂ line :=
    (differentiable_const v₀).add (differentiable_id.smul_const w)
  have hL (c : ℂ) : L (line c) = L v₀ := by
    simp only [line, L, map_add, map_smul, projectionAlong_self i w hw, smul_zero, add_zero]
  obtain ⟨C, _, hbound⟩ := HolomorphicAlgebraicity.Projection.Constructions.Cone.norm_le_projection hS hcone L
    (projectionAlong_kernel_trivial hcone i w hw hwS)
  have hcompact : IsCompact {c : ℂ | line c ∈ S} := by
    apply isCompact_iff_isClosed_bounded.mpr
    refine ⟨hS.preimage hline.continuous, ?_⟩
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨C * ‖L v₀‖ + ‖v₀ i‖, fun c hc => ?_⟩
    have hcoord : c = line c i - v₀ i := by simp [line, hw]
    calc
      ‖c‖ = ‖line c i - v₀ i‖ := congrArg norm hcoord
      _ ≤ ‖line c i‖ + ‖v₀ i‖ := norm_sub_le _ _
      _ ≤ ‖line c‖ + ‖v₀ i‖ := add_le_add (norm_le_pi_norm (line c) i) le_rfl
      _ ≤ C * ‖L v₀‖ + ‖v₀ i‖ := by
        exact add_le_add (by simpa only [hL] using hbound (line c) hc) le_rfl
  apply AnalyticFibers.Constructions.Cone.finite_of_isCompact_lineAnalytic hcompact
  intro c hc
  have hne : line c ≠ 0 := by
    intro hz
    apply hv₀
    rw [← hL c, hz, map_zero]
  obtain ⟨U, hU, hcU, m, f, hf, heq⟩ := hlocal (line c) hc hne
  have hpre : line ⁻¹' U ∈ 𝓝 c := (hU.preimage hline.continuous).mem_nhds hcU
  refine ⟨m, (fun k z => f k (line z)), (fun k => ?_), ?_⟩
  · exact ((hf k).comp hline.differentiableOn (mapsTo_preimage line U)).analyticAt hpre
  · filter_upwards [hpre] with z hz
    exact heq (line z) hz

/-- Every fiber is finite; the zero fiber is handled by the kernel condition,
so this does not assume any analytic extension across the cone vertex. -/
theorem finite_projectionAlong_fiber {S : Set (ι → ℂ)} (hS : IsClosed S)
    (hcone : ∀ (c : ℂ) ⦃v : ι → ℂ⦄, v ∈ S → c • v ∈ S)
    (i : ι) (w : ι → ℂ) (hw : w i = 1) (hwS : w ∉ S)
    (hlocal : ∀ v ∈ S, v ≠ 0 → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S v)
    (y : {j : ι // j ≠ i} → ℂ) :
    {v : ι → ℂ | v ∈ S ∧ projectionAlong i w v = y}.Finite := by
  by_cases hy : y = 0
  · subst y
    apply (finite_singleton (0 : ι → ℂ)).subset
    intro v hv
    exact projectionAlong_kernel_trivial hcone i w hw hwS v hv.1 hv.2
  by_cases hne : {v : ι → ℂ | v ∈ S ∧ projectionAlong i w v = y}.Nonempty
  · obtain ⟨v₀, hv₀⟩ := hne
    have hfin := finite_line_intersection hS hcone i w hw hwS hlocal v₀
      (by simpa only [hv₀.2] using hy)
    apply (hfin.image (fun c => v₀ + c • w)).subset
    intro v hv
    have hker : projectionAlong i w (v - v₀) = 0 := by
      rw [map_sub, hv.2, hv₀.2, sub_self]
    have heq := projectionAlong_kernel i w hw (v - v₀) hker
    have hline : v₀ + (v i - v₀ i) • w = v := by
      change v₀ + ((v - v₀) i) • w = v
      rw [← heq]
      abel
    refine ⟨v i - v₀ i, ?_, hline⟩
    change v₀ + (v i - v₀ i) • w ∈ S
    rw [hline]
    exact hv.1
  · rw [not_nonempty_iff_eq_empty.mp hne]
    exact finite_empty

end Projection

theorem rankTwoCenter_head (a₀ a₁ : ι) (b₀ b₁ : κ) (ha : a₀ ≠ a₁) :
    rankTwoCenter a₀ a₁ b₀ b₁ (a₀, b₀) = 1 := by
  classical
  simp [rankTwoCenter, ha]

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreProjection.Constructions.Segre
