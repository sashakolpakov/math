import Mathlib

/-! # Restricted Limits -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction

noncomputable section

section

/-! Restricted-product maps used to assemble local unitary actions.
Every map is constructed pointwise; no global splitting is an input. -/

open Filter
open scoped RestrictedProduct Classical

variable {I : Type*} {G H : I → Type*}
  [∀ v, Group (G v)] [∀ v, Group (H v)]
  (K : ∀ v, Subgroup (G v)) (L : ∀ v, Subgroup (H v))

abbrev RestrictedGroup := Πʳ v, [G v, K v]

def restrictedMap (f : ∀ v, G v →* H v)
    (hf : ∀ᶠ v in cofinite, Set.MapsTo (f v) (K v) (L v)) :
    RestrictedGroup K →* RestrictedGroup L :=
  RestrictedProduct.mapAlongMonoidHom G H id tendsto_id f hf

@[simp] theorem restrictedMap_apply (f : ∀ v, G v →* H v)
    (hf : ∀ᶠ v in cofinite, Set.MapsTo (f v) (K v) (L v))
    (g : RestrictedGroup K) (v : I) :
    restrictedMap K L f hf g v = f v (g v) := rfl

def includePlace (v : I) : G v →* RestrictedGroup K where
  toFun := RestrictedProduct.mulSingle K v
  map_one' := RestrictedProduct.mulSingle_one K v
  map_mul' := RestrictedProduct.mulSingle_mul K v

@[simp] theorem includePlace_same (v : I) (g : G v) :
    includePlace K v g v = g := RestrictedProduct.mulSingle_eq_same K v g

@[simp] theorem includePlace_other {v w : I} (h : w ≠ v) (g : G v) :
    includePlace K v g w = 1 := RestrictedProduct.mulSingle_eq_of_ne K g h

theorem includePlace_injective (v : I) : Function.Injective (includePlace K v) :=
  RestrictedProduct.mulSingle_injective K v

theorem restrictedMap_includePlace (f : ∀ v, G v →* H v)
    (hf : ∀ᶠ v in cofinite, Set.MapsTo (f v) (K v) (L v)) (v : I) (g : G v) :
    restrictedMap K L f hf (includePlace K v g) = includePlace L v (f v g) := by
  ext w
  by_cases h : w = v
  · subst w; simp
  · simp [h]

def diagonalMap {Q : Type*} [Group Q] (r : ∀ v, Q →* G v)
    (hr : ∀ q, ∀ᶠ v in cofinite, r v q ∈ K v) : Q →* RestrictedGroup K where
  toFun q := ⟨fun v => r v q, hr q⟩
  map_one' := by ext v; exact (r v).map_one
  map_mul' q q' := by ext v; exact (r v).map_mul q q'

@[simp] theorem diagonalMap_apply {Q : Type*} [Group Q] (r : ∀ v, Q →* G v)
    (hr : ∀ q, ∀ᶠ v in cofinite, r v q ∈ K v) (q : Q) (v : I) :
    diagonalMap K r hr q v = r v q := rfl

section Topology
variable [∀ v, TopologicalSpace (G v)] [∀ v, TopologicalSpace (H v)]

def restrictedContinuousMap (f : ∀ v, G v →ₜ* H v)
    (hf : ∀ᶠ v in cofinite, Set.MapsTo (f v) (K v) (L v)) :
    RestrictedGroup K →ₜ* RestrictedGroup L where
  toMonoidHom := restrictedMap K L (fun v => (f v).toMonoidHom) hf
  continuous_toFun := RestrictedProduct.mapAlong_continuous
    G H id tendsto_id (fun v => f v) hf (fun v => (f v).continuous)

theorem includePlace_continuous (v : I) : Continuous (includePlace K v) := by
  let f : G v → RestrictedProduct G (fun w => (K w : Set (G w)))
      (Filter.principal {w | w ≠ v}) := fun g =>
    ⟨Pi.mulSingle v g, by
      rw [Filter.eventually_principal]
      intro w hw
      simp [Pi.mulSingle_eq_of_ne hw]⟩
  have hf : Continuous f := by
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    exact continuous_mulSingle v
  have hco : cofinite ≤ Filter.principal {w : I | w ≠ v} := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite]
    simp
  exact (RestrictedProduct.continuous_inclusion hco).comp hf

def includePlaceContinuous (v : I) : G v →ₜ* RestrictedGroup K :=
  ⟨includePlace K v, includePlace_continuous K v⟩

end Topology

variable {A : I → Type*} [∀ v, AddGroup (A v)]
  [∀ v, TopologicalSpace (A v)] (J : ∀ v, AddSubgroup (A v))

def includeAddPlace (v : I) : A v →+ RestrictedProduct A (fun w => (J w : Set (A w))) cofinite where
  toFun := RestrictedProduct.single J v
  map_zero' := RestrictedProduct.single_zero J v
  map_add' := RestrictedProduct.single_add J v

theorem includeAddPlace_continuous (v : I) : Continuous (includeAddPlace J v) := by
  let f : A v → RestrictedProduct A (fun w => (J w : Set (A w)))
      (Filter.principal {w | w ≠ v}) := fun a =>
    ⟨Pi.single v a, by
      rw [Filter.eventually_principal]
      intro w hw
      simp [Pi.single_eq_of_ne hw]⟩
  have hf : Continuous f := by
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    exact continuous_single v
  have hco : cofinite ≤ Filter.principal {w : I | w ≠ v} := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite]
    simp
  exact (RestrictedProduct.continuous_inclusion hco).comp hf

end

/-! Truncations converge in the restricted product topology.
All truncations lie in one fixed principal stage, so coordinatewise
convergence suffices; no unrestricted product topology is substituted. -/

open Filter
open scoped Classical _root_.Topology

variable {I : Type*} {A : I → Type*} [∀ i, AddCommGroup (A i)]
  [∀ i, TopologicalSpace (A i)] (J : ∀ i, AddSubgroup (A i))

theorem restricted_sum_single_hasSum
    (x : RestrictedProduct A (fun i => (J i : Set (A i))) cofinite) :
    HasSum (fun i => RestrictedProduct.single J i (x i)) x := by
  let S : Set I := {i | x i ∈ J i}
  have hS : cofinite ≤ 𝓟 S := Filter.le_principal_iff.mpr x.property
  let y : RestrictedProduct A (fun i => (J i : Set (A i))) (𝓟 S) :=
    ⟨x, Filter.eventually_principal.mpr (fun _ hi => hi)⟩
  let t : Finset I → RestrictedProduct A (fun i => (J i : Set (A i))) (𝓟 S) :=
    fun s => ⟨fun i => if i ∈ s then x i else 0, by
      rw [Filter.eventually_principal]
      intro i hi
      change (if i ∈ s then x i else 0) ∈ J i
      split_ifs
      · exact hi
      · exact (J i).zero_mem⟩
  have ht : Tendsto t atTop (𝓝 y) := by
    apply RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff.mpr
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_atTop.2 ⟨{i}, fun s hs => hs⟩] with s hs
    change x i = if i ∈ s then x i else 0
    rw [ite_eq_left (hs (Finset.mem_singleton_self i))]
  have ht' := (RestrictedProduct.continuous_inclusion hS).tendsto y |>.comp ht
  have hy : RestrictedProduct.inclusion A (fun i => (J i : Set (A i))) hS y = x :=
    by apply RestrictedProduct.ext; intro i; rfl
  rw [hy] at ht'
  change Tendsto (fun s : Finset I => ∑ i ∈ s, RestrictedProduct.single J i (x i))
    atTop (𝓝 x)
  convert ht' using 1
  funext s
  apply RestrictedProduct.ext
  intro i
  change (∑ j ∈ s, RestrictedProduct.single J j (x j)) i =
    if i ∈ s then x i else 0
  change RestrictedProduct.evalAddMonoidHom A i
    (∑ j ∈ s, RestrictedProduct.single J j (x j)) = _
  rw [map_sum]
  by_cases hi : i ∈ s
  · rw [ite_eq_left hi, Finset.sum_eq_single i]
    · exact RestrictedProduct.single_eq_same J i (x i)
    · intro j _ hji
      exact RestrictedProduct.single_eq_of_ne J (x j) hji.symm
    · exact fun h => (h hi).elim
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro j hj
    exact RestrictedProduct.single_eq_of_ne J (x j) (fun h => hi (h ▸ hj))

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction
