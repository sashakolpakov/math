import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalKernel

namespace OAI.Algorithms

/-!
# Ordered enumeration from the emitted global columns

The orders are finite equivalences supplied by the actual coefficient-list
enumerator. Neither basis order nor coefficient order is replaced by a
canonical choice. Inverting an assignment uses the explicit local-pair
decompositions in `GlobalBasis.synthesis`.
-/

namespace SubexponentialSAT.Subexp.GlobalEnumeration

open scoped BigOperators
open BlockSearch LocalEnumeration GlobalBasis GlobalKernel ComputablePackingSplit

variable {K U V : Type*} [Field K] [DecidableEq K]
variable [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
variable {r b l : ℕ} {n m : Fin r → ℕ}
variable (color : U → Fin r) (sideIndex : ∀ g, Fin (n g) ≃ ColorFiber color g)
variable (constraint : ∀ g, Fin (m g) → Fin (n g) → K)
variable (pairs : ∀ g, Candidate K (n g) × Candidate K (n g))
variable (good : ∀ g, GoodPair (constraint g) (pairs g))
variable (alphabet : List K) (complete : ∀ x, x ∈ alphabet)
variable (packing : Fin b × U ↪ V) (leftovers : Fin l ≃ Leftover packing)

def outerEmbedding : OuterColumn (b := b) (l := l) pairs ↪ Column (b := b) (l := l) pairs :=
  ⟨Sum.inl, Sum.inl_injective⟩

def innerEmbedding (g : Fin r) : InnerColumn (b := b) pairs g ↪ Column (b := b) (l := l) pairs where
  toFun c := .inr ⟨g, c⟩
  inj' _ _ h := by simpa using h

def splitCoefficients : (Column (b := b) (l := l) pairs → K) ≃
    ((OuterColumn (b := b) (l := l) pairs → K) ×
      ((g : Fin r) → InnerColumn (b := b) pairs g → K)) where
  toFun x := (fun c => x (.inl c), fun g c => x (.inr ⟨g, c⟩))
  invFun x c := match c with
    | .inl c => x.1 c
    | .inr ⟨g, c⟩ => x.2 g c
  left_inv _ := by funext c; cases c <;> rfl
  right_inv _ := rfl

omit [DecidableEq K] in
theorem scatter_single {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) (a : A) :
    scatter e (Pi.single a (1 : K)) = Pi.single (e a) 1 := by
  funext y
  by_cases hy : y ∈ Set.range e
  · obtain ⟨z, rfl⟩ := hy
    rw [scatter_on_image]
    simp only [Pi.single_apply, e.injective.eq_iff]
  · rw [scatter_outside e _ y hy]
    have h : y ≠ e a := fun h => hy ⟨a, h.symm⟩
    simp only [Pi.single_apply, h, ite_false]

omit [DecidableEq K] in
theorem scatter_outer_at_inner (x : OuterColumn (b := b) (l := l) pairs → K)
    (g : Fin r) (c : InnerColumn (b := b) pairs g) :
    scatter (outerEmbedding pairs) x (.inr ⟨g, c⟩) = 0 := by
  apply scatter_outside
  rintro ⟨a, h⟩
  cases h

omit [DecidableEq K] in
theorem scatter_inner_at_outer (g : Fin r) (x : InnerColumn (b := b) pairs g → K)
    (c : OuterColumn (b := b) (l := l) pairs) :
    scatter (innerEmbedding (l := l) pairs g) x (.inl c) = 0 := by
  apply scatter_outside
  rintro ⟨a, h⟩
  cases h

omit [DecidableEq K] in
theorem scatter_inner_other (g h : Fin r) (hgh : g ≠ h)
    (x : InnerColumn (b := b) pairs g → K) (c : InnerColumn (b := b) pairs h) :
    scatter (innerEmbedding (l := l) pairs g) x (.inr ⟨h, c⟩) = 0 := by
  apply scatter_outside
  rintro ⟨a, ha⟩
  have hs : (⟨g, a⟩ : (j : Fin r) × InnerColumn (b := b) pairs j) = ⟨h, c⟩ := Sum.inr.inj ha
  exact hgh (congrArg Sigma.fst hs)

omit [DecidableEq K] in
/-- Split a full coefficient vector into its outer and per-color coordinates. -/
theorem coefficients_decomposition (x : Column (b := b) (l := l) pairs → K) :
    x = scatter (outerEmbedding pairs) ((splitCoefficients pairs x).1) +
      ∑ g, scatter (innerEmbedding (l := l) pairs g) ((splitCoefficients pairs x).2 g) := by
  funext c
  simp only [Pi.add_apply, Finset.sum_apply]
  cases c with
  | inl c =>
    have ho := scatter_on_image (outerEmbedding (b := b) (l := l) pairs)
      ((splitCoefficients pairs x).1) c
    change scatter (outerEmbedding pairs) ((splitCoefficients pairs x).1) (.inl c) = _ at ho
    rw [ho]
    simp only [scatter_inner_at_outer, Finset.sum_const_zero, add_zero]
    rfl
  | inr c =>
    rcases c with ⟨g, c⟩
    rw [scatter_outer_at_inner, zero_add]
    symm
    calc
      _ = scatter (innerEmbedding (l := l) pairs g) ((splitCoefficients pairs x).2 g)
          (.inr ⟨g, c⟩) := by
        apply Finset.sum_eq_single g
        · intro h _ hne
          exact scatter_inner_other pairs h g hne _ c
        · simp
      _ = _ := scatter_on_image (innerEmbedding (l := l) pairs g) _ c

def outerMap : (OuterColumn (b := b) (l := l) pairs → K) →ₗ[K] (V → K) :=
  (synthesisLinear color sideIndex constraint pairs good alphabet complete packing leftovers).toLinearMap.comp
    (scatter (outerEmbedding pairs))

def innerMap (g : Fin r) : (InnerColumn (b := b) pairs g → K) →ₗ[K] (V → K) :=
  (synthesisLinear color sideIndex constraint pairs good alphabet complete packing leftovers).toLinearMap.comp
    (scatter (innerEmbedding (l := l) pairs g))

omit [DecidableEq U] [Fintype V] in
theorem outerMap_reindexed_apply
    (x : Fin (outerList (b := b) (l := l) pairs).length → K) (v : V) :
    outerMap color sideIndex constraint pairs good alphabet complete packing leftovers
      (fun c => x ((outerEnumeration (b := b) (l := l) pairs).equivFin.symm c)) v =
      ∑ j, outerMatrix color sideIndex constraint pairs good alphabet complete packing leftovers v j * x j := by
  let e : Fin (outerList (b := b) (l := l) pairs).length ≃
      OuterColumn (b := b) (l := l) pairs :=
    (outerEnumeration (b := b) (l := l) pairs).equivFin
  let reindex : (Fin (outerList (b := b) (l := l) pairs).length → K) →ₗ[K]
      (OuterColumn (b := b) (l := l) pairs → K) :=
    { toFun := fun x c => x (e.symm c)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let F := (outerMap color sideIndex constraint pairs good alphabet complete packing leftovers).comp reindex
  have h := congrFun (LinearMap.pi_apply_eq_sum_univ F x) v
  change F x v = _
  rw [h]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  have hc : (fun c => if j = e.symm c then (1 : K) else 0) =
      Pi.single (e j) 1 := by
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
  change x j * (synthesisLinear color sideIndex constraint pairs good alphabet complete packing leftovers)
    (scatter (outerEmbedding pairs)
      (fun c => if j = e.symm c then 1 else 0)) v = _
  rw [hc, scatter_single]
  exact mul_comm _ _

omit [Fintype V] in
theorem innerMap_eq (g : Fin r) :
    innerMap color sideIndex constraint pairs good alphabet complete packing leftovers g =
      packedKernelLinear color sideIndex pairs packing g := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.pi_apply_eq_sum_univ _ x, LinearMap.pi_apply_eq_sum_univ _ x]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  have hs : (fun j : InnerColumn (b := b) pairs g => if c = j then (1 : K) else 0) =
      Pi.single c 1 := by
    funext j
    simp only [Pi.single_apply, eq_comm]
  rw [hs]
  change synthesisLinear color sideIndex constraint pairs good alphabet complete packing leftovers
    (scatter (innerEmbedding (l := l) pairs g) (Pi.single c 1)) = _
  rw [scatter_single]
  funext v
  exact (packedKernelLinear_single color sideIndex constraint pairs good packing alphabet complete leftovers g c v).symm

variable (G : Fin r → Submodule K (V → K))
variable (hG : ∀ g, DirectSums.packedSubspace packing (sideKernel color sideIndex constraint g) = G g)

include hG in
omit [Fintype V] in
theorem range_innerMap (g : Fin r) :
    LinearMap.range (innerMap color sideIndex constraint pairs good alphabet complete packing leftovers g) = G g := by
  rw [innerMap_eq, range_packedKernelLinear color sideIndex constraint pairs good packing, hG]

/-- The inverse reads the color's coordinates from the explicit full synthesis
inverse. No inverse of a global matrix is searched for. -/
def innerEquiv (g : Fin r) : (InnerColumn (b := b) pairs g → K) ≃ G g where
  toFun x := ⟨innerMap color sideIndex constraint pairs good alphabet complete packing leftovers g x, by
    rw [← range_innerMap color sideIndex constraint pairs good alphabet complete packing leftovers G hG g]
    exact ⟨x, rfl⟩⟩
  invFun z c := (synthesis color sideIndex constraint pairs good alphabet complete packing leftovers).symm
    z.val (.inr ⟨g, c⟩)
  left_inv x := by
    funext c
    change (synthesis color sideIndex constraint pairs good alphabet complete packing leftovers).symm
      ((synthesis color sideIndex constraint pairs good alphabet complete packing leftovers)
        (scatter (innerEmbedding (l := l) pairs g) x)) (.inr ⟨g, c⟩) = x c
    rw [Equiv.symm_apply_apply]
    exact scatter_on_image (innerEmbedding (l := l) pairs g) x c
  right_inv z := by
    have hm := congrArg (fun W : Submodule K (V → K) => (z.val : V → K) ∈ W)
      (range_innerMap color sideIndex constraint pairs good alphabet complete packing leftovers G hG g)
    have hz := Eq.mpr hm z.property
    obtain ⟨x, hx⟩ := hz
    apply Subtype.ext
    change innerMap color sideIndex constraint pairs good alphabet complete packing leftovers g
      (fun c => (synthesis color sideIndex constraint pairs good alphabet complete packing leftovers).symm
        z.val (.inr ⟨g, c⟩)) = z.val
    rw [← hx]
    congr 1
    funext c
    change (synthesis color sideIndex constraint pairs good alphabet complete packing leftovers).symm
      ((synthesis color sideIndex constraint pairs good alphabet complete packing leftovers)
        (scatter (innerEmbedding (l := l) pairs g) x)) (.inr ⟨g, c⟩) = x c
    rw [Equiv.symm_apply_apply]
    exact scatter_on_image (innerEmbedding (l := l) pairs g) x c

variable {outerCount : ℕ} {innerCount : Fin r → ℕ}
variable (outerOrder : Fin outerCount ≃ (OuterColumn (b := b) (l := l) pairs → K))
variable (innerOrder : ∀ g, Fin (innerCount g) ≃ (InnerColumn (b := b) pairs g → K))

/-- Any actual finite coefficient order yields layout enumeration data for
these same columns. The matrix-image enumerator supplies these orders. -/
def data : BlockwiseEnumeration.LocalData K V r G where
  outerCount := outerCount
  innerCount := innerCount
  outerBase o := outerMap color sideIndex constraint pairs good alphabet complete packing leftovers (outerOrder o)
  incrementEquiv g := (innerOrder g).trans
    (innerEquiv color sideIndex constraint pairs good alphabet complete packing leftovers G hG g)
  assignmentEquiv := (synthesis color sideIndex constraint pairs good alphabet complete packing leftovers).symm.trans
    ((splitCoefficients pairs).trans
      (Equiv.prodCongr outerOrder.symm (Equiv.piCongrRight fun g => (innerOrder g).symm)))
  reconstruction o x := by
    let c := (splitCoefficients pairs).symm (outerOrder o, fun g => innerOrder g (x g))
    have hd := coefficients_decomposition pairs c
    have hs := congrArg
      (synthesisLinear color sideIndex constraint pairs good alphabet complete packing leftovers) hd
    rw [map_add, map_sum] at hs
    exact hs

end SubexponentialSAT.Subexp.GlobalEnumeration

end OAI.Algorithms
