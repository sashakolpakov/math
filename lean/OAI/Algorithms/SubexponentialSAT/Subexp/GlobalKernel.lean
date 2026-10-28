import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasis

namespace OAI.Algorithms

/-!
# The emitted inner columns span the actual packed fixed space

The global matrix uses each successful local pair in its supplied side order.
This file identifies its color-specific column range. The only basis facts
used are the checks in `GoodPair`; every packing and coordinate map is the
one supplied to the matrix construction.
-/

namespace SubexponentialSAT.Subexp.GlobalKernel

open scoped BigOperators
open BlockSearch LocalEnumeration ComputablePackingSplit GlobalBasis

variable {K U V : Type*} [Field K] [DecidableEq K]
variable [Fintype U] [DecidableEq U] [DecidableEq V]
variable {r b l : ℕ} {n m : Fin r → ℕ}
variable (color : U → Fin r) (sideIndex : ∀ g, Fin (n g) ≃ ColorFiber color g)
variable (constraint : ∀ g, Fin (m g) → Fin (n g) → K)
variable (pairs : ∀ g, Candidate K (n g) × Candidate K (n g))
variable (good : ∀ g, GoodPair (constraint g) (pairs g))

def sideEmbedding (g : Fin r) : Fin (n g) ↪ U where
  toFun j := (sideIndex g j).val
  inj' _ _ h := (sideIndex g).injective (Subtype.ext h)

/-- The finite matrix kernel, copied into its actual ambient color side. -/
def sideKernel (g : Fin r) : Submodule K (U → K) :=
  (LinearMap.ker (matrixMap (constraint g))).map (scatter (sideEmbedding color sideIndex g))

omit [DecidableEq K] [Fintype U] in
theorem scatter_sideEmbedding_apply (g : Fin r) (x : Fin (n g) → K) (u : U) :
    scatter (sideEmbedding color sideIndex g) x u =
      if hu : color u = g then
        x ((sideIndex g).symm ⟨u, hu⟩)
      else 0 := by
  by_cases hu : color u = g
  · have he : sideEmbedding color sideIndex g ((sideIndex g).symm ⟨u, hu⟩) = u :=
      congrArg Subtype.val ((sideIndex g).apply_symm_apply ⟨u, hu⟩)
    rw [dite_eq_left hu]
    exact (congrArg (fun v => scatter (sideEmbedding color sideIndex g) x v) he).symm.trans
      (scatter_on_image (sideEmbedding color sideIndex g) x ((sideIndex g).symm ⟨u, hu⟩))
  · rw [dite_eq_right hu]
    apply scatter_outside
    rintro ⟨j, hj⟩
    exact hu (hj ▸ (sideIndex g j).property)

omit [DecidableEq K] [Fintype U] in
theorem mem_sideKernel_iff (g : Fin r) (y : U → K) :
    y ∈ sideKernel color sideIndex constraint g ↔
      (∀ u, color u ≠ g → y u = 0) ∧
      matrixMap (constraint g) (fun j => y (sideIndex g j).val) = 0 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor
    · intro u hu
      rw [scatter_sideEmbedding_apply, dite_eq_right hu]
    · have he : (fun j => scatter (sideEmbedding color sideIndex g) x (sideIndex g j).val) = x := by
        funext j
        exact scatter_on_image (sideEmbedding color sideIndex g) x j
      rw [he]
      exact hx
  · rintro ⟨hs, hk⟩
    refine ⟨(fun j => y (sideIndex g j).val), hk, ?_⟩
    funext u
    rw [scatter_sideEmbedding_apply]
    by_cases hu : color u = g
    · simp only [hu, dite_eq_left, Equiv.apply_symm_apply]
    · rw [dite_eq_right hu, hs u hu]

def localKernelLinear (g : Fin r) : (KernelIndex pairs g → K) →ₗ[K] (U → K) :=
  (scatter (sideEmbedding color sideIndex g)).comp (combineLinear (pairs g).1)

omit [DecidableEq K] [Fintype U] in
theorem localKernelLinear_apply (g : Fin r) (x : KernelIndex pairs g → K) (u : U) :
    localKernelLinear color sideIndex pairs g x u =
      if hu : color u = g then
        combine (pairs g).1 x ((sideIndex g).symm ⟨u, hu⟩)
      else 0 :=
  scatter_sideEmbedding_apply color sideIndex g (combine (pairs g).1 x) u

include good in
omit [DecidableEq K] [Fintype U] in
theorem range_localKernelLinear (g : Fin r) :
    LinearMap.range (localKernelLinear color sideIndex pairs g) =
      sideKernel color sideIndex constraint g := by
  have hc : LinearMap.range (combineLinear (pairs g).1) =
      LinearMap.ker (matrixMap (constraint g)) := by
    ext x
    exact ((good g).1.mem_kernel_iff x).symm
  rw [localKernelLinear, LinearMap.range_comp, hc]
  rfl

variable (packing : Fin b × U ↪ V)

/-- Block copies of the actual local kernel columns. -/
def packedKernelLinear (g : Fin r) :
    (InnerColumn (b := b) pairs g → K) →ₗ[K] (V → K) := by
  let blockMap : (InnerColumn (b := b) pairs g → K) →ₗ[K] (Fin b × U → K) :=
    { toFun := fun x z => localKernelLinear color sideIndex pairs g (fun j => x (z.1, j)) z.2
      map_add' := by
        intro x y
        funext z
        exact congrFun (map_add (localKernelLinear color sideIndex pairs g) _ _) z.2
      map_smul' := by
        intro a x
        funext z
        exact congrFun (map_smul (localKernelLinear color sideIndex pairs g) a _) z.2 }
  exact (scatter packing).comp blockMap

omit [DecidableEq K] in
@[simp] theorem packedKernelLinear_on_block (g : Fin r)
    (x : InnerColumn (b := b) pairs g → K) (block : Fin b) (u : U) :
    packedKernelLinear color sideIndex pairs packing g x (packing (block, u)) =
      localKernelLinear color sideIndex pairs g (fun j => x (block, j)) u :=
  scatter_on_image packing _ (block, u)

omit [DecidableEq K] in
theorem packedKernelLinear_outside (g : Fin r)
    (x : InnerColumn (b := b) pairs g → K) (v : V) (hv : v ∉ Set.range packing) :
    packedKernelLinear color sideIndex pairs packing g x v = 0 :=
  scatter_outside packing _ v hv

include good in
omit [DecidableEq K] in
/-- No global search is needed: each block restriction is represented by its
already checked local kernel tuple. -/
theorem range_packedKernelLinear (g : Fin r) :
    LinearMap.range (packedKernelLinear color sideIndex pairs packing g) =
      DirectSums.packedSubspace packing (sideKernel color sideIndex constraint g) := by
  classical
  ext y
  rw [DirectSums.mem_packedSubspace_iff]
  constructor
  · rintro ⟨x, rfl⟩
    constructor
    · intro block
      rw [← range_localKernelLinear color sideIndex constraint pairs good g]
      refine ⟨fun j => x (block, j), ?_⟩
      funext u
      exact (packedKernelLinear_on_block color sideIndex pairs packing g x block u).symm
    · intro v hv
      exact packedKernelLinear_outside color sideIndex pairs packing g x v hv
  · intro hy
    have hlocal : ∀ block : Fin b, ∃ x : KernelIndex pairs g → K,
        localKernelLinear color sideIndex pairs g x = (fun u => y (packing (block, u))) := by
      intro block
      have h := hy.1 block
      rw [← range_localKernelLinear color sideIndex constraint pairs good g] at h
      exact h
    choose x hx using hlocal
    refine ⟨fun z => x z.1 z.2, ?_⟩
    funext v
    by_cases hv : v ∈ Set.range packing
    · obtain ⟨⟨block, u⟩, rfl⟩ := hv
      rw [packedKernelLinear_on_block]
      exact congrFun (hx block) u
    · rw [packedKernelLinear_outside color sideIndex pairs packing g _ v hv, hy.2 v hv]

variable (alphabet : List K) (complete : ∀ x, x ∈ alphabet)
variable (leftovers : Fin l ≃ Leftover packing)

/-- The literal inner column in `GlobalBasis` is the corresponding block
copy of the checked local kernel column. -/
theorem packedKernelLinear_single (g : Fin r) (c : InnerColumn (b := b) pairs g) (v : V) :
    packedKernelLinear color sideIndex pairs packing g (Pi.single c 1) v =
      matrix color sideIndex constraint pairs good alphabet complete packing leftovers v (.inr ⟨g, c⟩) := by
  rcases c with ⟨block', j⟩
  by_cases hv : v ∈ Set.range packing
  · obtain ⟨⟨block, u⟩, rfl⟩ := hv
    rw [packedKernelLinear_on_block, localKernelLinear_apply, matrix_kernel_column]
    by_cases hu : color u = g
    · rw [dite_eq_left hu, dite_eq_left hu]
      by_cases hb : block = block'
      · subst block'
        simp [combine, Pi.single_apply, ite_apply]
      · simp [combine, hb]
    · rw [dite_eq_right hu, dite_eq_right hu]
  · rw [packedKernelLinear_outside color sideIndex pairs packing g _ v hv]
    rw [matrix_leftover color sideIndex constraint pairs good alphabet complete packing leftovers ⟨v, hv⟩]
    simp

/-- Reindex the coefficient columns using the exact ordered list emitted by
the dense assembler. This reindexing does not change their range. -/
def indexedKernelLinear (g : Fin r) :
    (Fin (innerList (b := b) pairs g).length → K) →ₗ[K] (V → K) := by
  let reindex : (Fin (innerList (b := b) pairs g).length → K) →ₗ[K]
      (InnerColumn (b := b) pairs g → K) :=
    { toFun := fun x c => x ((innerEnumeration (b := b) pairs g).equivFin.symm c)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact (packedKernelLinear color sideIndex pairs packing g).comp reindex

theorem indexedKernelLinear_apply (g : Fin r)
    (x : Fin (innerList (b := b) pairs g).length → K) (v : V) :
    indexedKernelLinear color sideIndex pairs packing g x v =
      ∑ j, innerMatrix color sideIndex constraint pairs good alphabet complete packing leftovers g v j * x j := by
  let e : Fin (innerList (b := b) pairs g).length ≃ InnerColumn (b := b) pairs g :=
    (innerEnumeration (b := b) pairs g).equivFin
  have hc : ∀ j : Fin (innerList (b := b) pairs g).length,
      (fun c => (if j = e.symm c then (1 : K) else 0)) = Pi.single (e j) 1 := by
    intro j
    funext c
    by_cases h : c = e j
    · subst c
      simp
    · have hj : j ≠ e.symm c := by
        intro hj
        apply h
        calc
          c = e (e.symm c) := (e.apply_symm_apply c).symm
          _ = e j := congrArg e hj.symm
      simp [h, hj]
  have h := congrFun (LinearMap.pi_apply_eq_sum_univ
    (indexedKernelLinear color sideIndex pairs packing g) x) v
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j _
  change x j * packedKernelLinear color sideIndex pairs packing g
    (fun c => if j = e.symm c then 1 else 0) v = _
  rw [hc, packedKernelLinear_single color sideIndex constraint pairs good packing alphabet complete leftovers]
  exact mul_comm _ _

include good in
omit [DecidableEq K] in
theorem range_indexedKernelLinear (g : Fin r) :
    LinearMap.range (indexedKernelLinear color sideIndex pairs packing g) =
      DirectSums.packedSubspace packing (sideKernel color sideIndex constraint g) := by
  rw [← range_packedKernelLinear color sideIndex constraint pairs good packing g]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨fun c => x ((innerEnumeration (b := b) pairs g).equivFin.symm c), rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨fun j => x ((innerEnumeration (b := b) pairs g).equivFin j), ?_⟩
    change packedKernelLinear color sideIndex pairs packing g
      (fun c => x ((innerEnumeration (b := b) pairs g).equivFin
        ((innerEnumeration (b := b) pairs g).equivFin.symm c))) = _
    simp only [Equiv.apply_symm_apply]

section ActualConstraints

variable {Δ : ℕ} (g : Fin r) (J : Fin Δ → Set U)
variable (hJ : ∀ i, J i ⊆ {u | color u = g}) [∀ i, Fintype (J i)]
variable (M : (i : Fin Δ) → (J i → K) →ₗ[K] (J i → K))
variable (rowE : Fin (m g) ≃ ((i : Fin Δ) × J i))

omit [DecidableEq K] [Fintype U] [(i : Fin Δ) → Fintype (J i)] in
/-- The range characterization above specializes to the actual fixed space
when the local matrix consists of the encoded joint constraints. -/
theorem sideKernel_eq_supported
    (hconstraint : constraint g = SubspaceDimension.encodedConstraintMatrix
      {u | color u = g} J hJ M rowE (sideIndex g)) :
    sideKernel color sideIndex constraint g =
      SubexponentialSAT.SubspaceDimension.supportedFixedSpace {u | color u = g} J hJ M := by
  ext y
  rw [mem_sideKernel_iff, SubexponentialSAT.SubspaceDimension.mem_supportedFixedSpace_iff]
  have hk : matrixMap (constraint g) (fun j => y (sideIndex g j).val) = 0 ↔
      (fun u : ColorFiber color g => y u.val) ∈
        SubexponentialSAT.SubspaceDimension.coordinateFixedSpace {u | color u = g} J hJ M := by
    rw [hconstraint]
    change (fun a => ∑ j, SubspaceDimension.encodedConstraintMatrix
      {u | color u = g} J hJ M rowE (sideIndex g) a j * y (sideIndex g j).val) = 0 ↔ _
    rw [funext_iff]
    have he : (fun u : ColorFiber color g => y ((sideIndex g) ((sideIndex g).symm u)).val) =
        (fun u : ColorFiber color g => y u.val) := by
      funext u
      exact congrArg (fun z : ColorFiber color g => y z.val) ((sideIndex g).apply_symm_apply u)
    have hzero := SubspaceDimension.encodedConstraintMatrix_zero_iff
      {u | color u = g} J hJ M rowE (sideIndex g) (fun j => y (sideIndex g j).val)
    have hmem := congrArg
      (fun f : ColorFiber color g → K =>
        f ∈ SubexponentialSAT.SubspaceDimension.coordinateFixedSpace {u | color u = g} J hJ M) he
    constructor
    · intro hz
      exact Eq.mp hmem (hzero.mp hz)
    · intro hz
      exact hzero.mpr (Eq.mpr hmem hz)
  rw [hk]
  apply and_congr Iff.rfl
  rw [SubexponentialSAT.SubspaceDimension.mem_coordinateFixedSpace]
  rfl

include good in
omit [DecidableEq K] [(i : Fin Δ) → Fintype (J i)] in
/-- The actual color-specific numeric columns span exactly the packed
fixed space used by the layout, for any successful local pairs and any
explicit side/joint enumeration order. -/
theorem range_indexedKernelLinear_supported
    (hconstraint : constraint g = SubspaceDimension.encodedConstraintMatrix
      {u | color u = g} J hJ M rowE (sideIndex g)) :
    LinearMap.range (indexedKernelLinear color sideIndex pairs packing g) =
      DirectSums.packedSubspace packing
        (SubexponentialSAT.SubspaceDimension.supportedFixedSpace {u | color u = g} J hJ M) := by
  rw [range_indexedKernelLinear color sideIndex constraint pairs good packing g,
    sideKernel_eq_supported color sideIndex constraint g J hJ M rowE hconstraint]

end ActualConstraints

section Universal

open SubexponentialSAT.MulticolorTypes

variable {Q Δ : ℕ}
variable (t : Fin Q)
variable (M : (g : Fin r) → (i : Fin Δ) →
  (Joint t g i → K) →ₗ[K] (Joint t g i → K))
variable (rowE : ∀ g, Fin (m g) ≃ ((i : Fin Δ) × Joint t g i))
variable (colE : ∀ g, Fin (n g) ≃ Side (Δ := Δ) t g)

def universalConstraint (g : Fin r) : Fin (m g) → Fin (n g) → K :=
  SubspaceDimension.encodedConstraintMatrix (side t g) (joint t g)
    (joint_subset_side t g) (M g) (rowE g) (colE g)

omit [DecidableEq K] in
/-- In particular, the explicit inner matrices span the exact universal
fixed spaces copied into the actual block packing. All numerical constraint
identities are discharged by the definition of `universalConstraint`. -/
theorem range_universal_indexedKernelLinear
    (packed : Fin b × UniversalType r Q Δ ↪ V)
    (hpairs : ∀ g, GoodPair (universalConstraint t M rowE colE g) (pairs g))
    (g : Fin r) :
    LinearMap.range (indexedKernelLinear (fun u : UniversalType r Q Δ => u.head t)
      colE pairs packed g) =
      DirectSums.packedSubspace packed (SubspaceDimension.universalFixedSpace t g (M g)) :=
  range_indexedKernelLinear_supported (fun u : UniversalType r Q Δ => u.head t)
    colE (universalConstraint t M rowE colE) pairs hpairs packed g
    (joint t g) (joint_subset_side t g) (M g) (rowE g) rfl

end Universal

end SubexponentialSAT.Subexp.GlobalKernel

end OAI.Algorithms
