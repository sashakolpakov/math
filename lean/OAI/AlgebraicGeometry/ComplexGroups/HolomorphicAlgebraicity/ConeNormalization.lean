import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LinearAnalyticImage
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LinearFiberCardinality

/-! # Cone Normalization -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity

noncomputable section

/-!
# Dimension reduction for a closed analytic cone

Every proper cone containing zero admits a normalized center outside it.
Projection along that center lowers the ambient coordinate dimension and
preserves closedness, scaling invariance, finite fibers, and analyticity
away from zero.
-/

open Set Filter _root_.Metric _root_.Complex
open scoped _root_.Topology

theorem ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt.image_equiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {S : Set E} {x : E} (hlocal : ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S x) (e : E ≃L[ℂ] F) :
    ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (e '' S) (e x) := by
  have h : ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S (e.symm (e x)) := by simpa only [e.symm_apply_apply] using hlocal
  have hp := h.preimage (g := e.symm) isOpen_univ (mem_univ _) e.symm.differentiable.differentiableOn
  change ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (e.toHomeomorph '' S) (e x)
  rw [e.toHomeomorph.image_eq_preimage_symm]
  exact hp

def ConeNormalization.Constructions.Cone.omittedCoordinateEquiv {n : ℕ} (i : Fin (n + 1)) :
    ({j : Fin (n + 1) // j ≠ i} → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
  { toLinearMap := (SegreAt.Constructions.Segre.contractFin i).toLinearMap
    invFun := SegreAt.Constructions.Segre.expandFin i
    left_inv := by intro v; ext j; simp [SegreAt.Constructions.Segre.contractFin, SegreAt.Constructions.Segre.expandFin]
    right_inv := SegreAt.Constructions.Segre.contractFin_expandFin i }

theorem ConeNormalization.Constructions.Cone.exists_normalized_center {n : ℕ} {S : Set (Fin (n + 1) → ℂ)}
    (hzero : 0 ∈ S) (hcone : ∀ (c : ℂ) ⦃v⦄, v ∈ S → c • v ∈ S) (hne : S ≠ univ) :
    ∃ (i : Fin (n + 1)) (w : Fin (n + 1) → ℂ), w i = 1 ∧ w ∉ S := by
  classical
  obtain ⟨v, hv⟩ := (Set.ne_univ_iff_exists_notMem S).mp hne
  have hv0 : v ≠ 0 := by intro h; exact hv (h.symm ▸ hzero)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
  change v i ≠ 0 at hi
  let w := (v i)⁻¹ • v
  refine ⟨i, w, by simp [w, hi], ?_⟩
  intro hw
  apply hv
  have hscale : (v i) • w = v := by
    simp only [w, smul_smul, mul_inv_cancel₀ hi, one_smul]
  exact hscale ▸ hcone (v i) hw

theorem ConeNormalization.Constructions.Cone.exists_projection_step {n : ℕ} {S : Set (Fin (n + 1) → ℂ)}
    (hzero : 0 ∈ S) (hS : IsClosed S)
    (hcone : ∀ (c : ℂ) ⦃v⦄, v ∈ S → c • v ∈ S)
    (hlocal : ∀ v ∈ S, v ≠ 0 → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S v) (hne : S ≠ univ) :
    ∃ L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin n → ℂ),
      IsProperMap (fun v : S => L v) ∧
      (∀ y, {v | v ∈ S ∧ L v = y}.Finite) ∧
      (∃ N : ℕ, ∀ y, {v | v ∈ S ∧ L v = y}.ncard ≤ N) ∧
      (∀ v ∈ S, L v = 0 → v = 0) ∧
      0 ∈ L '' S ∧ IsClosed (L '' S) ∧
      (∀ (c : ℂ) ⦃y⦄, y ∈ L '' S → c • y ∈ L '' S) ∧
      ∀ y, y ≠ 0 → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (L '' S) y := by
  obtain ⟨i, w, hw, hwS⟩ := ConeNormalization.Constructions.Cone.exists_normalized_center hzero hcone hne
  let b := ConeNormalization.Constructions.Cone.omittedCoordinateEquiv i
  let L₀ := SegreProjection.Constructions.Segre.projectionAlong i w
  let L := b.toContinuousLinearMap.comp L₀
  have hproper : IsProperMap (fun v : S => L v) :=
    b.toHomeomorph.isProperMap.comp (SegreProjection.Constructions.Segre.isProperMap_projectionAlong hS hcone i w hw hwS)
  refine ⟨L, hproper, ?_, ?_, ?_, ⟨0, hzero, map_zero L⟩, ?_, ?_, ?_⟩
  · intro y
    have hfin := SegreProjection.Constructions.Segre.finite_projectionAlong_fiber hS hcone i w hw hwS hlocal (b.symm y)
    apply hfin.subset
    intro v hv
    refine ⟨hv.1, ?_⟩
    exact b.injective (by simpa only [L, L₀, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, b.apply_symm_apply] using hv.2)
  · obtain ⟨N, hN⟩ := LinearFiberCardinality.Constructions.Segre.bounded_fiber_cardinality_projectionAlong hS hcone i w hw hwS hlocal
    refine ⟨N, fun y => ?_⟩
    have hs : {v | v ∈ S ∧ L v = y} ⊆ {v | v ∈ S ∧ L₀ v = b.symm y} := by
      intro v hv
      exact ⟨hv.1, b.injective (by simpa only [L, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, b.apply_symm_apply] using hv.2)⟩
    exact (ncard_le_ncard hs
      (SegreProjection.Constructions.Segre.finite_projectionAlong_fiber hS hcone i w hw hwS hlocal (b.symm y))).trans (hN (b.symm y))
  · intro v hv hL
    exact SegreProjection.Constructions.Segre.projectionAlong_kernel_trivial hcone i w hw hwS v hv
      (b.injective (by simpa only [L, L₀, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, map_zero] using hL))
  · rw [Set.image_eq_range]
    exact hproper.isClosedMap.isClosed_range
  · intro c y hy
    obtain ⟨v, hv, rfl⟩ := hy
    exact ⟨c • v, hcone c hv, map_smul L c v⟩
  · intro y hy
    have hby : b.symm y ≠ 0 := by
      intro h
      exact hy (by simpa only [b.apply_symm_apply, map_zero] using congrArg b h)
    have h := (LinearAnalyticImage.Constructions.Segre.holomorphicZeroSetAt_projectionAlong hS hcone i w hw hwS hlocal
      (b.symm y) hby).image_equiv b
    simpa only [L, L₀, Set.image_image, b.apply_symm_apply, Function.comp_def,
      ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe] using h

/-- Iterated dimension reduction supplies a finite proper linear projection
onto a full coordinate space. The projection has no nonzero cone point in
its kernel. No analyticity at the vertex is used. -/
theorem ConeNormalization.Constructions.Cone.exists_finite_surjective_projection {n : ℕ} {S : Set (Fin n → ℂ)}
    (hzero : 0 ∈ S) (hS : IsClosed S)
    (hcone : ∀ (c : ℂ) ⦃v⦄, v ∈ S → c • v ∈ S)
    (hlocal : ∀ v ∈ S, v ≠ 0 → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S v) :
    ∃ (d : ℕ) (L : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)), d ≤ n ∧
      IsProperMap (fun v : S => L v) ∧
      (∀ y, {v | v ∈ S ∧ L v = y}.Finite) ∧
      (∃ N : ℕ, ∀ y, {v | v ∈ S ∧ L v = y}.ncard ≤ N) ∧
      (∀ v ∈ S, L v = 0 → v = 0) ∧ L '' S = univ := by
  classical
  induction n with
  | zero =>
    have hfull : S = univ := by
      apply eq_univ_of_forall
      intro v
      exact (Subsingleton.elim (0 : Fin 0 → ℂ) v) ▸ hzero
    refine ⟨0, ContinuousLinearMap.id ℂ _, le_rfl, hS.isProperMap_subtypeVal,
      ?_, ?_, fun _ _ h => h, ?_⟩
    · intro y
      exact (finite_singleton y).subset (fun v hv => hv.2)
    · refine ⟨1, fun y => ?_⟩
      simpa only [ncard_singleton] using
        ncard_le_ncard (t := {y}) (fun v hv => hv.2) (finite_singleton y)
    · change id '' S = univ
      rwa [image_id]
  | succ n ih =>
    by_cases hfull : S = univ
    · refine ⟨n + 1, ContinuousLinearMap.id ℂ _, le_rfl, hS.isProperMap_subtypeVal,
        ?_, ?_, fun _ _ h => h, ?_⟩
      · intro y
        exact (finite_singleton y).subset (fun v hv => hv.2)
      · refine ⟨1, fun y => ?_⟩
        simpa only [ncard_singleton] using
          ncard_le_ncard (t := {y}) (fun v hv => hv.2) (finite_singleton y)
      · change id '' S = univ
        rwa [image_id]
    obtain ⟨L₁, hp₁, hf₁, ⟨N, hN⟩, hk₁, hz₁, hc₁, hs₁, ha₁⟩ :=
      ConeNormalization.Constructions.Cone.exists_projection_step hzero hS hcone hlocal hfull
    let T := L₁ '' S
    obtain ⟨d, L₂, hd, hp₂, hf₂, ⟨M, hM⟩, hk₂, honto⟩ := ih hz₁ hc₁ hs₁ (fun y _ hy => ha₁ y hy)
    let f : S → T := fun v => ⟨L₁ v, ⟨v, v.property, rfl⟩⟩
    have hfc : Continuous f :=
      (L₁.continuous.comp continuous_subtype_val).subtype_mk _
    have hfp : IsProperMap f := isProperMap_of_comp_of_inj hfc continuous_subtype_val hp₁
      Subtype.val_injective
    refine ⟨d, L₂.comp L₁, hd.trans (Nat.le_succ n), hp₂.comp hfp, ?_, ?_, ?_, ?_⟩
    · intro y
      have hfin := (hf₂ y).biUnion (fun u _ => hf₁ u)
      apply hfin.subset
      intro v hv
      refine mem_iUnion.mpr ⟨L₁ v, mem_iUnion.mpr ⟨?_, ⟨hv.1, rfl⟩⟩⟩
      exact ⟨⟨v, hv.1, rfl⟩, hv.2⟩
    · exact ⟨M * N, fun y => (LinearFiberCardinality.Constructions.Cone.finite_bounded_fiber_comp (S := S) (T := T) L₁ L₂
        (fun v hv => ⟨v, hv, rfl⟩) hf₁ hf₂ hN hM y).2⟩
    · intro v hv hL
      exact hk₁ v hv (hk₂ (L₁ v) ⟨v, hv, rfl⟩ hL)
    · change (fun v => L₂ (L₁ v)) '' S = univ
      rw [← Set.image_image]
      exact honto

theorem ConeNormalization.Constructions.Cone.exists_finite_surjective_projection_finiteDimensional
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {S : Set E} (hzero : 0 ∈ S) (hS : IsClosed S)
    (hcone : ∀ (c : ℂ) ⦃v⦄, v ∈ S → c • v ∈ S)
    (hlocal : ∀ v ∈ S, v ≠ 0 → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S v) :
    ∃ (d : ℕ) (L : E →L[ℂ] (Fin d → ℂ)), d ≤ Module.finrank ℂ E ∧
      IsProperMap (fun v : S => L v) ∧
      (∀ y, {v | v ∈ S ∧ L v = y}.Finite) ∧
      (∃ N : ℕ, ∀ y, {v | v ∈ S ∧ L v = y}.ncard ≤ N) ∧ L '' S = univ ∧
      ∃ C : ℝ, 0 < C ∧ ∀ v ∈ S, ‖v‖ ≤ C * ‖L v‖ := by
  let e := (Module.finBasis ℂ E).equivFunL
  let T := e '' S
  have hzT : 0 ∈ T := ⟨0, hzero, map_zero e⟩
  have hcT : IsClosed T := e.toHomeomorph.isClosedMap S hS
  have hsT : ∀ (c : ℂ) ⦃v⦄, v ∈ T → c • v ∈ T := by
    intro c v hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨c • w, hcone c hw, map_smul e c w⟩
  have haT : ∀ v ∈ T, v ≠ 0 → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt T v := by
    intro v hv hv0
    obtain ⟨w, hw, rfl⟩ := hv
    exact (hlocal w hw (fun hw0 => hv0 (by simp [hw0]))).image_equiv e
  obtain ⟨d, L, hd, hp, hf, ⟨N, hN⟩, hk, honto⟩ := ConeNormalization.Constructions.Cone.exists_finite_surjective_projection hzT hcT hsT haT
  let L' := L.comp e.toContinuousLinearMap
  let h : S ≃ₜ T := e.toHomeomorph.image S
  have hker : ∀ v ∈ S, L' v = 0 → v = 0 := by
    intro v hv hLv
    exact e.injective (by simpa only [map_zero] using hk (e v) ⟨v, hv, rfl⟩ hLv)
  refine ⟨d, L', hd, hp.comp h.isProperMap, ?_, ?_, ?_, Projection.Constructions.Cone.norm_le_projection hS hcone L' hker⟩
  · intro y
    have hpre := (hf y).preimage (f := e) e.injective.injOn
    exact hpre.subset (fun v hv => ⟨⟨v, hv.1, rfl⟩, hv.2⟩)
  · refine ⟨N, fun y => ?_⟩
    exact (ncard_le_ncard_of_injOn (s := {v | v ∈ S ∧ L' v = y})
      (t := {u | u ∈ T ∧ L u = y}) e (fun v hv => ⟨⟨v, hv.1, rfl⟩, hv.2⟩)
      e.injective.injOn (hf y)).trans (hN y)
  · change (fun v => L (e v)) '' S = univ
    rw [← Set.image_image]
    exact honto

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity
