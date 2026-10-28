import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains

/-! # Spatial Pushforward -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SpatialPushforward.Cycles.SpatialSupport

noncomputable section

/-!
# Functoriality of spatially locally finite pushforwards

The composition law is proved by collecting a finite set of contributing
source coefficients over each target index. Finiteness is supplied by spatial
local finiteness and nonempty target images, rather than assumed globally.
-/

open Set Function
open scoped BigOperators

variable {X ι κ μ : Type*} [TopologicalSpace X]
variable {R : Type*} [Semiring R]

/-- Summing over the fibers of the identity preserves every coefficient. -/
@[simp]
theorem fiberSum_id (c : ι → R) : LocallyFiniteChains.Cycles.SpatialSupport.fiberSum id c = c := by
  funext i
  simp [LocallyFiniteChains.Cycles.SpatialSupport.fiberSum]

/-- Nested fiber sums collect exactly the coefficients in the composite
fiber, whenever its nonzero source coefficients form a finite set. -/
theorem fiberSum_comp_of_finite (f : ι → κ) (g : κ → μ) (c : ι → R) (k : μ)
    (h : ({i | g (f i) = k} ∩ support c).Finite) :
    LocallyFiniteChains.Cycles.SpatialSupport.fiberSum g (LocallyFiniteChains.Cycles.SpatialSupport.fiberSum f c) k = LocallyFiniteChains.Cycles.SpatialSupport.fiberSum (g ∘ f) c k := by
  classical
  let s : Finset ι := h.toFinset
  have hs (i : ι) : i ∈ s ↔ g (f i) = k ∧ c i ≠ 0 := by
    simp only [s, Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Function.mem_support]
  have houter : LocallyFiniteChains.Cycles.SpatialSupport.fiberSum g (LocallyFiniteChains.Cycles.SpatialSupport.fiberSum f c) k =
      ∑ j ∈ s.image f, LocallyFiniteChains.Cycles.SpatialSupport.fiberSum f c j := by
    apply finsum_mem_eq_sum_of_subset
    · rintro j ⟨hgj, hj⟩
      obtain ⟨i, hfi, hci⟩ := exists_ne_zero_of_finsum_mem_ne_zero hj
      exact Finset.mem_image.mpr ⟨i, (hs i).mpr ⟨hfi.symm ▸ hgj, hci⟩, hfi⟩
    · intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact ((hs i).mp hi).1
  have hinner (j : κ) (hj : g j = k) :
      LocallyFiniteChains.Cycles.SpatialSupport.fiberSum f c j = ∑ i ∈ s with f i = j, c i := by
    apply finsum_mem_eq_sum_of_subset
    · rintro i ⟨hfi, hci⟩
      exact Finset.mem_filter.mpr ⟨(hs i).mpr ⟨hfi.symm ▸ hj, hci⟩, hfi⟩
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  calc
    LocallyFiniteChains.Cycles.SpatialSupport.fiberSum g (LocallyFiniteChains.Cycles.SpatialSupport.fiberSum f c) k = ∑ j ∈ s.image f, LocallyFiniteChains.Cycles.SpatialSupport.fiberSum f c j := houter
    _ = ∑ j ∈ s.image f, ∑ i ∈ s with f i = j, c i := by
      apply Finset.sum_congr rfl
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact hinner (f i) ((hs i).mp hi).1
    _ = ∑ i ∈ s, c i :=
      Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem f hi) c
    _ = LocallyFiniteChains.Cycles.SpatialSupport.fiberSum (g ∘ f) c k := (finsum_mem_eq_sum c h).symm

/-- The identity index map induces the identity linear map on spatially
locally finite chains. -/
@[simp]
theorem pushforward_id (imageA : ι → Set X)
    (hneA : ∀ i, (imageA i).Nonempty) :
    LocallyFiniteChains.Cycles.SpatialSupport.pushforward (R := R) id (fun _ => Subset.rfl) hneA =
      (LinearMap.id : LocallyFiniteChains.Cycles.SpatialSupport.module R imageA →ₗ[R] LocallyFiniteChains.Cycles.SpatialSupport.module R imageA) := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  exact fiberSum_id (c : ι → R)

/-- Index-map equality gives equality of the induced linear maps; the
containment certificates do not affect the pushforward coefficients. -/
theorem pushforward_congr {imageA : ι → Set X} {imageB : κ → Set X}
    {f g : ι → κ} (hfg : f = g)
    (hf : ∀ i, imageB (f i) ⊆ imageA i)
    (hg : ∀ i, imageB (g i) ⊆ imageA i)
    (hneB : ∀ j, (imageB j).Nonempty) :
    LocallyFiniteChains.Cycles.SpatialSupport.pushforward (R := R) f hf hneB = LocallyFiniteChains.Cycles.SpatialSupport.pushforward g hg hneB := by
  subst g
  rfl

/-- Composition of the actual finite-fiber linear pushforwards agrees with
pushforward along the composite index map. -/
theorem pushforward_comp {imageA : ι → Set X} {imageB : κ → Set X}
    {imageC : μ → Set X} (f : ι → κ) (g : κ → μ)
    (hf : ∀ i, imageB (f i) ⊆ imageA i)
    (hg : ∀ j, imageC (g j) ⊆ imageB j)
    (hneB : ∀ j, (imageB j).Nonempty)
    (hneC : ∀ k, (imageC k).Nonempty) :
    (LocallyFiniteChains.Cycles.SpatialSupport.pushforward (R := R) g hg hneC).comp (LocallyFiniteChains.Cycles.SpatialSupport.pushforward f hf hneB) =
      LocallyFiniteChains.Cycles.SpatialSupport.pushforward (g ∘ f) (fun i => (hg (f i)).trans (hf i)) hneC := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  funext k
  change LocallyFiniteChains.Cycles.SpatialSupport.fiberSum g (LocallyFiniteChains.Cycles.SpatialSupport.fiberSum f (c : ι → R)) k = LocallyFiniteChains.Cycles.SpatialSupport.fiberSum (g ∘ f) c k
  apply fiberSum_comp_of_finite
  exact LocallyFiniteChains.Cycles.SpatialSupport.finite_fiber (g ∘ f) (fun i => (hg (f i)).trans (hf i)) hneC c k

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SpatialPushforward.Cycles.SpatialSupport
