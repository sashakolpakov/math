import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.FiberCardinality
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LinearAnalyticImage

/-! # Linear Fiber Cardinality -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LinearFiberCardinality

noncomputable section

/-!
# Uniform fiber bounds for linear cone projections

Transport the coordinate-projection cardinality bound through linear
coordinates and apply it to projections along a center outside the cone.
-/

open Set Filter _root_.Metric _root_.Complex
open scoped _root_.Topology

namespace Constructions.Cone

open scoped BigOperators in
theorem finite_bounded_fiber_comp
    {X Y Z : Type*} {S : Set X} {T : Set Y} (f : X → Y) (g : Y → Z)
    (hmap : MapsTo f S T)
    (hf : ∀ y, {x | x ∈ S ∧ f x = y}.Finite)
    (hg : ∀ z, {y | y ∈ T ∧ g y = z}.Finite) {N M : ℕ}
    (hN : ∀ y, {x | x ∈ S ∧ f x = y}.ncard ≤ N)
    (hM : ∀ z, {y | y ∈ T ∧ g y = z}.ncard ≤ M) (z : Z) :
    {x | x ∈ S ∧ g (f x) = z}.Finite ∧ {x | x ∈ S ∧ g (f x) = z}.ncard ≤ M * N := by
  classical
  let K := (hg z).toFinset
  let H := K.biUnion (fun y => (hf y).toFinset)
  have hsub : {x | x ∈ S ∧ g (f x) = z} ⊆ (H : Set X) := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨f x, (hg z).mem_toFinset.mpr ⟨hmap hx.1, hx.2⟩,
      (hf (f x)).mem_toFinset.mpr ⟨hx.1, rfl⟩⟩
  have hK : K.card ≤ M := by
    rw [← ncard_eq_toFinset_card _ (hg z)]
    exact hM z
  have hH : H.card ≤ M * N := by
    apply Finset.card_biUnion_le.trans
    calc
      ∑ y ∈ K, (hf y).toFinset.card ≤ ∑ _y ∈ K, N := by
        apply Finset.sum_le_sum
        intro y _
        rw [← ncard_eq_toFinset_card _ (hf y)]
        exact hN y
      _ = K.card * N := by simp
      _ ≤ M * N := Nat.mul_le_mul_right N hK
  exact ⟨H.finite_toSet.subset hsub,
    (ncard_le_ncard hsub H.finite_toSet).trans (by simpa only [ncard_coe_finset] using hH)⟩

theorem bounded_fiber_cardinality_linear_projection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (e : E ≃L[ℂ] ((Fin n → ℂ) × ℂ)) {S : Set E}
    (hproper : IsProperMap (fun p : S => (e p.val).1))
    (hfinite : ∀ x, {v : E | v ∈ S ∧ (e v).1 = x}.Finite)
    (hcone : ∀ (a : ℂ) ⦃v⦄, v ∈ S → a • v ∈ S)
    (hlocal : ∀ v ∈ S, v ≠ 0 → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S v) :
    ∃ N : ℕ, ∀ x, {v : E | v ∈ S ∧ (e v).1 = x}.ncard ≤ N := by
  let T := e.symm ⁻¹' S
  let h : T ≃ₜ S := e.symm.toHomeomorph.subtype (fun _ => Iff.rfl)
  have hproperT : IsProperMap (fun p : T => p.val.1) := by
    convert hproper.comp h.isProperMap using 1
    funext p
    exact (congrArg Prod.fst (e.apply_symm_apply p.val)).symm
  have hinj (x : Fin n → ℂ) : Function.Injective (fun z : ℂ => e.symm (x, z)) := by
    intro a b hab
    exact congrArg Prod.snd (e.symm.injective hab)
  have hfiniteT (x : Fin n → ℂ) : {z : ℂ | (x, z) ∈ T}.Finite := by
    have ht := (hfinite x).preimage (hinj x).injOn
    convert ht using 1
    ext z
    simp only [T, mem_preimage, mem_ofPred_eq, e.apply_symm_apply, and_true]
  have hconeT : ∀ (a : ℂ) ⦃v⦄, v ∈ T → a • v ∈ T := by
    intro a v hv
    change e.symm (a • v) ∈ S
    rw [map_smul]
    exact hcone a hv
  have hlocalT : ∀ v ∈ T, v ≠ 0 → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt T v := by
    intro v hv hv0
    have hev : e.symm v ≠ 0 := fun h => hv0 (by simpa only [e.apply_symm_apply, map_zero] using congrArg e h)
    exact (hlocal (e.symm v) hv hev).preimage isOpen_univ (mem_univ _)
      e.symm.differentiable.differentiableOn
  obtain ⟨N, hN⟩ := FiberCardinality.Constructions.Cone.bounded_fiber_cardinality_of_cone hproperT hfiniteT hconeT hlocalT
  refine ⟨N, fun x => ?_⟩
  have heq : {v : E | v ∈ S ∧ (e v).1 = x} =
      (fun z : ℂ => e.symm (x, z)) '' {z : ℂ | (x, z) ∈ T} := by
    ext v
    constructor
    · rintro ⟨hv, hvx⟩
      refine ⟨(e v).2, ?_, ?_⟩
      · change e.symm (x, (e v).2) ∈ S
        rw [← hvx]
        simpa only [Prod.eta, e.symm_apply_apply] using hv
      · rw [← hvx]
        exact e.symm_apply_apply v
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hz, by simp⟩
  rw [heq, ncard_image_of_injective _ (hinj x)]
  exact hN x

end Constructions.Cone

namespace Constructions.Segre

theorem bounded_fiber_cardinality_projectionAlong
    {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Set (ι → ℂ)}
    (hS : IsClosed S) (hcone : ∀ (c : ℂ) ⦃v⦄, v ∈ S → c • v ∈ S)
    (i : ι) (w : ι → ℂ) (hw : w i = 1) (hwS : w ∉ S)
    (hlocal : ∀ v ∈ S, v ≠ 0 → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S v) :
    ∃ N : ℕ, ∀ y, {v | v ∈ S ∧ SegreProjection.Constructions.Segre.projectionAlong i w v = y}.ncard ≤ N := by
  let F := {j : ι // j ≠ i} → ℂ
  let b := (Module.finBasis ℂ F).equivFunL
  let e := (LinearAnalyticImage.Constructions.Segre.projectionAlongEquiv i w).trans (b.prodCongr (ContinuousLinearEquiv.refl ℂ ℂ))
  have he (v : ι → ℂ) : (e v).1 = b (SegreProjection.Constructions.Segre.projectionAlong i w v) := rfl
  have hp : IsProperMap (fun v : S => (e v.val).1) :=
    b.toHomeomorph.isProperMap.comp (SegreProjection.Constructions.Segre.isProperMap_projectionAlong hS hcone i w hw hwS)
  have hf (x : Fin (Module.finrank ℂ F) → ℂ) : {v | v ∈ S ∧ (e v).1 = x}.Finite := by
    have h := SegreProjection.Constructions.Segre.finite_projectionAlong_fiber hS hcone i w hw hwS hlocal (b.symm x)
    apply h.subset
    intro v hv
    exact ⟨hv.1, b.injective (by simpa only [he, b.apply_symm_apply] using hv.2)⟩
  obtain ⟨N, hN⟩ := Cone.bounded_fiber_cardinality_linear_projection e hp hf hcone hlocal
  refine ⟨N, fun y => ?_⟩
  simpa only [he, b.injective.eq_iff] using hN (b y)

end Constructions.Segre

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LinearFiberCardinality
