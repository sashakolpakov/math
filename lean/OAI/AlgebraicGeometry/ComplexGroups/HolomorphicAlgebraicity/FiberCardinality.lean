import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProperAnalyticImage

/-! # Fiber Cardinality -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.FiberCardinality.Constructions.Cone

noncomputable section

/-!
# Local bounds on the cardinalities of proper analytic fibers

Each local prepared polynomial bounds the number of roots in its disk.
Properness ensures finitely many such disks cover all nearby fibers.
-/

open Set Filter _root_.Metric _root_.Complex _root_.Polynomial
open scoped _root_.Topology BigOperators

theorem eventually_fiber_mem_disk_union {n : ℕ} {S : Set ((Fin n → ℂ) × ℂ)}
    {x : Fin n → ℂ} (hproper : IsProperMap (fun p : S => p.val.1))
    (R : {z : ℂ | (x, z) ∈ S} → ℝ) (hR : ∀ a, 0 < R a) :
    ∀ᶠ y in 𝓝 x, ∀ z, (y, z) ∈ S →
      ∃ a : {z : ℂ | (x, z) ∈ S}, z ∈ ball (a : ℂ) (R a) := by
  let O : Set ((Fin n → ℂ) × ℂ) :=
    ⋃ a : {z : ℂ | (x, z) ∈ S}, Prod.snd ⁻¹' ball (a : ℂ) (R a)
  have hO : IsOpen O := isOpen_iUnion (fun a => isOpen_ball.preimage continuous_snd)
  let D : Set S := Subtype.val ⁻¹' Oᶜ
  have hD : IsClosed D := hO.isClosed_compl.preimage continuous_subtype_val
  have hclosed := hproper.isClosedMap D hD
  have hxnot : x ∉ (fun p : S => p.val.1) '' D := by
    rintro ⟨⟨⟨y, z⟩, hyz⟩, hpD, hpx⟩
    dsimp only at hpx
    subst y
    exact hpD (mem_iUnion.mpr ⟨⟨z, hyz⟩, mem_ball_self (hR ⟨z, hyz⟩)⟩)
  filter_upwards [hclosed.isOpen_compl.mem_nhds hxnot] with y hy
  intro z hyz
  have hyo : (y, z) ∈ O := by
    by_contra hnot
    exact hy ⟨⟨(y, z), hyz⟩, hnot, rfl⟩
  obtain ⟨a, ha⟩ := mem_iUnion.mp hyo
  exact ⟨a, ha⟩

theorem exists_local_polynomial_bound {n : ℕ} {S : Set ((Fin n → ℂ) × ℂ)}
    {x : Fin n → ℂ} {c : ℂ} (hlocal : ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S (x, c))
    (hfinite : {z : ℂ | (x, z) ∈ S}.Finite) :
    ∃ (R : ℝ) (d : ℕ) (U : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → Polynomial ℂ),
      0 < R ∧ IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, (P y).Monic ∧ (P y).natDegree = d ∧
        ∀ z ∈ closedBall c R, (y, z) ∈ S → (P y).eval z = 0 := by
  obtain ⟨R, d, m, U, Q, hR, hU, hx, _, _, hQ, heq⟩ :=
    PolynomialFibers.Constructions.Preparation.polynomial_equations_of_finite_fiber hlocal hfinite
  exact ⟨R, d, U, Q 0, hR, hU, hx, fun y hy =>
    ⟨(hQ y hy).1, (hQ y hy).2.1, fun z hz hzs => ((heq y hy z hz).mp hzs) 0⟩⟩

theorem eventually_bounded_fiber_cardinality {n : ℕ}
    {S : Set ((Fin n → ℂ) × ℂ)} {x : Fin n → ℂ}
    (hproper : IsProperMap (fun p : S => p.val.1))
    (hfinite : {z : ℂ | (x, z) ∈ S}.Finite)
    (hlocal : ∀ z, (x, z) ∈ S → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S (x, z)) :
    ∃ N : ℕ, ∀ᶠ y in 𝓝 x, {z : ℂ | (y, z) ∈ S}.Finite ∧
      {z : ℂ | (y, z) ∈ S}.ncard ≤ N := by
  classical
  let K := {z : ℂ | (x, z) ∈ S}
  let : Fintype K := hfinite.fintype
  have hprep := fun a : K => exists_local_polynomial_bound (hlocal a a.property) hfinite
  choose R d U P hR hU hx hP using hprep
  have hcover := eventually_fiber_mem_disk_union hproper R hR
  have hnear : ∀ᶠ y in 𝓝 x, ∀ a : K, y ∈ U a :=
    eventually_all.mpr (fun a => (hU a).mem_nhds (hx a))
  refine ⟨∑ a : K, d a, ?_⟩
  filter_upwards [hcover, hnear] with y hy hUy
  let H : Finset ℂ := Finset.univ.biUnion (fun a : K => (P a y).roots.toFinset)
  have hsub : {z : ℂ | (y, z) ∈ S} ⊆ (H : Set ℂ) := by
    intro z hz
    obtain ⟨a, ha⟩ := hy z hz
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, Multiset.mem_toFinset.mpr
      ((mem_roots (hP a y (hUy a)).1.ne_zero).mpr
        ((hP a y (hUy a)).2.2 z (ball_subset_closedBall ha) hz))⟩
  have hcard : H.card ≤ ∑ a : K, d a := by
    apply (Finset.card_biUnion_le).trans
    apply Finset.sum_le_sum
    intro a _
    exact (Multiset.toFinset_card_le _).trans
      ((card_roots' (P a y)).trans_eq (hP a y (hUy a)).2.1)
  refine ⟨H.finite_toSet.subset hsub, ?_⟩
  exact (ncard_le_ncard hsub H.finite_toSet).trans (by simpa only [ncard_coe_finset] using hcard)

theorem bounded_on_compact_of_locally_bounded {X : Type*} [TopologicalSpace X]
    {s : Set X} (hs : IsCompact s) {b : X → ℕ}
    (hlocal : ∀ x ∈ s, ∃ N : ℕ, ∀ᶠ y in 𝓝 x, b y ≤ N) :
    ∃ N : ℕ, ∀ x ∈ s, b x ≤ N := by
  classical
  choose N hN using (fun a : s => hlocal a a.property)
  have hopen := fun a : s => _root_.mem_nhds_iff.mp (hN a)
  choose U hUb hU hxU using hopen
  have hcover : s ⊆ ⋃ a : s, U a := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  obtain ⟨t, ht⟩ := hs.elim_finite_subcover U hU hcover
  refine ⟨t.sup N, fun x hx => ?_⟩
  obtain ⟨a, hxa⟩ := mem_iUnion.mp (ht hx)
  obtain ⟨ha, hxa⟩ := mem_iUnion.mp hxa
  exact (hUb a hxa).trans (Finset.le_sup ha)

theorem fiber_eq_scaled_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {S : Set (E × ℂ)} (hcone : ∀ (a : ℂ) ⦃v⦄, v ∈ S → a • v ∈ S)
    {a : ℂ} (ha : a ≠ 0) (y : E) :
    {z : ℂ | (a • y, z) ∈ S} = (fun z : ℂ => a * z) '' {z : ℂ | (y, z) ∈ S} := by
  ext z
  constructor
  · intro hz
    refine ⟨a⁻¹ * z, ?_, mul_inv_cancel_left₀ ha z⟩
    change (y, a⁻¹ * z) ∈ S
    have h := hcone a⁻¹ hz
    simpa only [Prod.smul_mk, smul_smul, inv_mul_cancel₀ ha, one_smul, smul_eq_mul] using h
  · rintro ⟨w, hw, rfl⟩
    exact hcone a hw

theorem fiber_ncard_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {S : Set (E × ℂ)} (hcone : ∀ (a : ℂ) ⦃v⦄, v ∈ S → a • v ∈ S)
    {a : ℂ} (ha : a ≠ 0) (y : E) :
    {z : ℂ | (a • y, z) ∈ S}.ncard = {z : ℂ | (y, z) ∈ S}.ncard := by
  rw [fiber_eq_scaled_image hcone ha y]
  exact ncard_image_of_injective _ (mul_right_injective₀ ha)

/-- Scaling reduces a global fiber-cardinality bound to compactness of the
unit sphere; the vertex fiber is handled separately. -/
theorem bounded_fiber_cardinality_of_cone {n : ℕ}
    {S : Set ((Fin n → ℂ) × ℂ)}
    (hproper : IsProperMap (fun p : S => p.val.1))
    (hfinite : ∀ y, {z : ℂ | (y, z) ∈ S}.Finite)
    (hcone : ∀ (a : ℂ) ⦃v⦄, v ∈ S → a • v ∈ S)
    (hlocal : ∀ v ∈ S, v ≠ 0 → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S v) :
    ∃ N : ℕ, ∀ y, {z : ℂ | (y, z) ∈ S}.ncard ≤ N := by
  have hb : ∀ y ∈ sphere (0 : Fin n → ℂ) 1,
      ∃ N : ℕ, ∀ᶠ x in 𝓝 y, {z : ℂ | (x, z) ∈ S}.ncard ≤ N := by
    intro y hy
    have hy0 : y ≠ 0 := by
      intro h
      simp only [h, mem_sphere, dist_self, zero_ne_one] at hy
    obtain ⟨N, hN⟩ := eventually_bounded_fiber_cardinality hproper (hfinite y)
      (fun z hz => hlocal (y, z) hz (fun h => hy0 (congrArg Prod.fst h)))
    exact ⟨N, hN.mono (fun _ h => h.2)⟩
  obtain ⟨N, hN⟩ := bounded_on_compact_of_locally_bounded (isCompact_sphere (0 : Fin n → ℂ) 1) hb
  refine ⟨max N {z : ℂ | ((0 : Fin n → ℂ), z) ∈ S}.ncard, fun y => ?_⟩
  by_cases hy : y = 0
  · subst y
    exact le_max_right _ _
  let a : ℂ := (‖y‖ : ℂ)⁻¹
  have ha : a ≠ 0 := inv_ne_zero (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hy))
  have hunit : a • y ∈ sphere (0 : Fin n → ℂ) 1 := by
    rw [mem_sphere_iff_norm, sub_zero, norm_smul]
    simp [a, norm_ne_zero_iff.mpr hy]
  rw [← fiber_ncard_smul hcone ha y]
  exact (hN (a • y) hunit).trans (le_max_left _ _)

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.FiberCardinality.Constructions.Cone
