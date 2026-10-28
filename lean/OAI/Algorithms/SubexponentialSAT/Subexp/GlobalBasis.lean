import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalEnumeration
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking

namespace OAI.Algorithms

/-!
# Explicit global columns from the actual local pairs

No basis is selected in this file. Each side supplies the pair returned by
its finite search, together with that search's actual side enumeration.
Global columns copy those tuples into the packed blocks and add the leftover
standard coordinates. This is the algebraic specification of the dense
matrix assembler; it is not a cost model for emitting its entries.
-/

namespace SubexponentialSAT.Subexp.GlobalBasis

open scoped BigOperators
open BlockSearch LocalEnumeration ComputablePackingSplit

variable {K U V : Type*} [Field K] [DecidableEq K]
variable [Fintype U] [DecidableEq V]
variable {r b l : ℕ} {n m : Fin r → ℕ}
variable (color : U → Fin r) (sideIndex : ∀ g, Fin (n g) ≃ ColorFiber color g)
variable (constraint : ∀ g, Fin (m g) → Fin (n g) → K)
variable (pairs : ∀ g, Candidate K (n g) × Candidate K (n g))
variable (good : ∀ g, GoodPair (constraint g) (pairs g))
variable (alphabet : List K) (complete : ∀ x, x ∈ alphabet)

abbrev KernelIndex (g : Fin r) := Fin (pairs g).1.1.val
abbrev ComplementIndex (g : Fin r) := Fin (pairs g).2.1.val
abbrev LocalOuter := (g : Fin r) × ComplementIndex pairs g

/-- The column order within these index types is specified by explicit lists
below: leftovers first, then blocks, colors, and local complement columns. -/
abbrev OuterColumn := Fin l ⊕ (Fin b × LocalOuter pairs)
abbrev InnerColumn (g : Fin r) := Fin b × KernelIndex pairs g
abbrev Column := OuterColumn (b := b) (l := l) pairs ⊕
  ((g : Fin r) × InnerColumn (b := b) pairs g)

def localOuterList : List (LocalOuter pairs) :=
  (List.finRange r).sigma (fun g => List.finRange (pairs g).2.1.val)

omit [Field K] [DecidableEq K] in
theorem localOuterList_nodup : (localOuterList pairs).Nodup :=
  (List.nodup_finRange r).sigma (fun g => List.nodup_finRange (pairs g).2.1.val)

omit [Field K] [DecidableEq K] in
theorem mem_localOuterList (c : LocalOuter pairs) : c ∈ localOuterList pairs :=
  List.mem_sigma.mpr ⟨List.mem_finRange c.1, List.mem_finRange c.2⟩

def outerList : List (OuterColumn (b := b) (l := l) pairs) :=
  (List.finRange l).map Sum.inl ++
    (((List.finRange b).product (localOuterList pairs)).map Sum.inr)

def innerList (g : Fin r) : List (InnerColumn (b := b) pairs g) :=
  (List.finRange b).product (List.finRange (pairs g).1.1.val)

omit [Field K] [DecidableEq K] in
theorem outerList_nodup : (outerList (b := b) (l := l) pairs).Nodup := by
  apply List.Nodup.append
  · exact (List.nodup_finRange l).map Sum.inl_injective
  · exact ((List.nodup_finRange b).product (localOuterList_nodup pairs)).map Sum.inr_injective
  · apply List.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨a', _, he⟩ := List.mem_map.mp hy
    cases he

omit [Field K] [DecidableEq K] in
theorem mem_outerList (c : OuterColumn (b := b) (l := l) pairs) :
    c ∈ outerList pairs := by
  cases c with
  | inl j => simp [outerList]
  | inr c =>
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨c, List.mem_product.mpr
      ⟨List.mem_finRange c.1, mem_localOuterList pairs c.2⟩, rfl⟩

def outerEnumeration : ConstructivePacking.FiniteEnumeration
    (OuterColumn (b := b) (l := l) pairs) :=
  ⟨outerList pairs, outerList_nodup pairs, mem_outerList pairs⟩

def innerEnumeration (g : Fin r) : ConstructivePacking.FiniteEnumeration
    (InnerColumn (b := b) pairs g) where
  values := innerList pairs g
  nodup := (List.nodup_finRange b).product (List.nodup_finRange (pairs g).1.1.val)
  complete c := List.mem_product.mpr ⟨List.mem_finRange c.1, List.mem_finRange c.2⟩

def localCoordinates : (U → K) ≃
    ((g : Fin r) → (KernelIndex pairs g → K) × (ComplementIndex pairs g → K)) :=
  (partitionEquiv color).trans (Equiv.piCongrRight fun g =>
    (BlockwiseEnumeration.reindexFunction (sideIndex g)).trans
      (pairEquiv alphabet complete (pairs g) (good g)))

omit [Fintype U] in
theorem localCoordinates_symm_apply
    (z : (g : Fin r) → (KernelIndex pairs g → K) × (ComplementIndex pairs g → K))
    (u : U) :
    (localCoordinates color sideIndex constraint pairs good alphabet complete).symm z u =
      combine (pairs (color u)).1 (z (color u)).1
        ((sideIndex (color u)).symm ⟨u, rfl⟩) +
      combine (pairs (color u)).2 (z (color u)).2
        ((sideIndex (color u)).symm ⟨u, rfl⟩) := rfl

variable (packing : Fin b × U ↪ V)
variable (leftovers : Fin l ≃ Leftover packing)

/-- A full coefficient vector is synthesized by the local searched pairs
and the explicit packing. Both directions are given by concrete maps. -/
def synthesis : (Column (b := b) (l := l) pairs → K) ≃ (V → K) where
  toFun x := assemble packing
    ((fun block => (localCoordinates color sideIndex constraint pairs good alphabet complete).symm
      (fun g => ((fun j => x (.inr ⟨g, (block, j)⟩)),
        fun j => x (.inl (.inr (block, ⟨g, j⟩)))))),
      fun v => x (.inl (.inl (leftovers.symm v))))
  invFun y col := match col with
    | .inl (.inl j) => y (leftovers j).val
    | .inl (.inr (block, ⟨g, j⟩)) =>
        ((localCoordinates color sideIndex constraint pairs good alphabet complete)
          (fun u => y (packing (block, u))) g).2 j
    | .inr ⟨g, (block, j)⟩ =>
        ((localCoordinates color sideIndex constraint pairs good alphabet complete)
          (fun u => y (packing (block, u))) g).1 j
  left_inv x := by
    funext col
    cases col with
    | inl col =>
      cases col with
      | inl j =>
        dsimp only
        rw [assemble_outside packing _ (leftovers j).val (leftovers j).property]
        change x (.inl (.inl (leftovers.symm (leftovers j)))) = x (.inl (.inl j))
        simp only [Equiv.symm_apply_apply]
      | inr col =>
        rcases col with ⟨block, g, j⟩
        simp
    | inr col =>
      rcases col with ⟨g, block, j⟩
      simp
  right_inv y := by
    apply (split packing).injective
    apply Prod.ext
    · funext block u
      simp
    · funext v
      change assemble packing _ v.val = y v.val
      rw [assemble_outside packing _ v.val v.property]
      exact congrArg (fun w : Leftover packing => y w.val)
        (leftovers.apply_symm_apply v)

theorem synthesis_block (x : Column (b := b) (l := l) pairs → K) (block : Fin b) (u : U) :
    synthesis color sideIndex constraint pairs good alphabet complete packing leftovers x
      (packing (block, u)) =
      combine (pairs (color u)).1 (fun j => x (.inr ⟨color u, (block, j)⟩))
        ((sideIndex (color u)).symm ⟨u, rfl⟩) +
      combine (pairs (color u)).2 (fun j => x (.inl (.inr (block, ⟨color u, j⟩))))
        ((sideIndex (color u)).symm ⟨u, rfl⟩) := by
  exact (assemble_on_block packing _ block u).trans
    (localCoordinates_symm_apply color sideIndex constraint pairs good alphabet complete _ u)

theorem synthesis_leftover (x : Column (b := b) (l := l) pairs → K)
    (v : Leftover packing) :
    synthesis color sideIndex constraint pairs good alphabet complete packing leftovers x v.val =
      x (.inl (.inl (leftovers.symm v))) :=
  assemble_outside packing _ v.val v.property

/-- The explicit synthesis is linear; its inverse already comes from the
actual successful local decompositions. -/
def synthesisLinear : (Column (b := b) (l := l) pairs → K) ≃ₗ[K] (V → K) where
  toEquiv := synthesis color sideIndex constraint pairs good alphabet complete packing leftovers
  map_add' x y := by
    funext v
    change synthesis color sideIndex constraint pairs good alphabet complete packing leftovers (x + y) v =
      synthesis color sideIndex constraint pairs good alphabet complete packing leftovers x v +
        synthesis color sideIndex constraint pairs good alphabet complete packing leftovers y v
    by_cases hv : v ∈ Set.range packing
    · obtain ⟨⟨block, u⟩, rfl⟩ := hv
      simp only [synthesis_block, Pi.add_apply]
      simp [combine, Finset.sum_add_distrib, add_mul, Pi.smul_apply]
      ring
    · rw [synthesis_leftover color sideIndex constraint pairs good alphabet complete packing leftovers
        (x + y) ⟨v, hv⟩,
        synthesis_leftover color sideIndex constraint pairs good alphabet complete packing leftovers x ⟨v, hv⟩,
        synthesis_leftover color sideIndex constraint pairs good alphabet complete packing leftovers y ⟨v, hv⟩]
      rfl
  map_smul' a x := by
    funext v
    change synthesis color sideIndex constraint pairs good alphabet complete packing leftovers (a • x) v =
      a * synthesis color sideIndex constraint pairs good alphabet complete packing leftovers x v
    by_cases hv : v ∈ Set.range packing
    · obtain ⟨⟨block, u⟩, rfl⟩ := hv
      simp only [synthesis_block, Pi.smul_apply, smul_eq_mul]
      simp [combine, Pi.smul_apply, Finset.mul_sum, mul_add, mul_assoc]
    · rw [synthesis_leftover color sideIndex constraint pairs good alphabet complete packing leftovers
        (a • x) ⟨v, hv⟩,
        synthesis_leftover color sideIndex constraint pairs good alphabet complete packing leftovers x ⟨v, hv⟩]
      rfl

/-- One column is the image of its standard coefficient coordinate. -/
def matrix (v : V) (col : Column (b := b) (l := l) pairs) : K :=
  synthesisLinear color sideIndex constraint pairs good alphabet complete packing leftovers
    (Pi.single col 1) v

/-- Row-major matrices use the literal enumeration lists consumed by the
assembler: no arbitrary finite-type enumeration appears here. -/
def outerMatrix (v : V)
    (j : Fin (outerList (b := b) (l := l) pairs).length) : K :=
  matrix color sideIndex constraint pairs good alphabet complete packing leftovers v
    (.inl ((outerEnumeration pairs).equivFin j))

def innerMatrix (g : Fin r) (v : V)
    (j : Fin (innerList (b := b) pairs g).length) : K :=
  matrix color sideIndex constraint pairs good alphabet complete packing leftovers v
    (.inr ⟨g, (innerEnumeration pairs g).equivFin j⟩)

theorem matrix_mul (x : Column (b := b) (l := l) pairs → K) (v : V) :
    (∑ col, matrix color sideIndex constraint pairs good alphabet complete packing leftovers v col * x col) =
      synthesis color sideIndex constraint pairs good alphabet complete packing leftovers x v := by
  let S := synthesisLinear color sideIndex constraint pairs good alphabet complete packing leftovers
  have hsingle (col : Column (b := b) (l := l) pairs) :
      (fun j : Column (b := b) (l := l) pairs => if col = j then (1 : K) else 0) =
        Pi.single col 1 := by
    funext j
    simp only [Pi.single_apply, eq_comm]
  have h := congrFun (LinearMap.pi_apply_eq_sum_univ S.toLinearMap x) v
  change (∑ col, S (Pi.single col 1) v * x col) = S x v
  simpa only [hsingle, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm,
    LinearEquiv.coe_coe] using h.symm

theorem matrix_leftover (v : Leftover packing) (col : Column (b := b) (l := l) pairs) :
    matrix color sideIndex constraint pairs good alphabet complete packing leftovers v.val col =
      if col = .inl (.inl (leftovers.symm v)) then 1 else 0 := by
  change synthesis color sideIndex constraint pairs good alphabet complete packing leftovers
      (Pi.single col 1) v.val = _
  rw [synthesis_leftover]
  by_cases h : col = .inl (.inl (leftovers.symm v))
  · subst col
    rw [Pi.single_eq_same, ite_eq_left rfl]
  · rw [Pi.single_eq_of_ne (Ne.symm h), ite_eq_right h]

theorem matrix_leftover_column (block : Fin b) (u : U) (j : Fin l) :
    matrix color sideIndex constraint pairs good alphabet complete packing leftovers
      (packing (block, u)) (.inl (.inl j)) = 0 := by
  change synthesis color sideIndex constraint pairs good alphabet complete packing leftovers
      (Pi.single (.inl (.inl j)) 1) (packing (block, u)) = _
  rw [synthesis_block]
  simp [combine]

theorem matrix_kernel_column (block block' : Fin b) (u : U) (g : Fin r)
    (j : KernelIndex pairs g) :
    matrix color sideIndex constraint pairs good alphabet complete packing leftovers
      (packing (block, u)) (.inr ⟨g, (block', j)⟩) =
      if h : color u = g then
        if block = block' then (pairs g).1.2 j ((sideIndex g).symm ⟨u, h⟩) else 0
      else 0 := by
  change synthesis color sideIndex constraint pairs good alphabet complete packing leftovers
      (Pi.single (.inr ⟨g, (block', j)⟩) 1) (packing (block, u)) = _
  rw [synthesis_block]
  by_cases hg : color u = g
  · subst g
    by_cases hb : block = block'
    · subst block'
      simp [combine, Pi.single_apply, ite_apply]
    · simp [combine, hb]
  · simp [combine, hg]

theorem matrix_complement_column (block block' : Fin b) (u : U) (g : Fin r)
    (j : ComplementIndex pairs g) :
    matrix color sideIndex constraint pairs good alphabet complete packing leftovers
      (packing (block, u)) (.inl (.inr (block', ⟨g, j⟩))) =
      if h : color u = g then
        if block = block' then (pairs g).2.2 j ((sideIndex g).symm ⟨u, h⟩) else 0
      else 0 := by
  change synthesis color sideIndex constraint pairs good alphabet complete packing leftovers
      (Pi.single (.inl (.inr (block', ⟨g, j⟩))) 1) (packing (block, u)) = _
  rw [synthesis_block]
  by_cases hg : color u = g
  · subst g
    by_cases hb : block = block'
    · subst block'
      simp [combine, Pi.single_apply, ite_apply]
    · simp [combine, hb]
  · simp [combine, hg]

/-- The columns are a complete independent coordinate system because the
inverse is restriction followed by the checked local decomposition. -/
theorem existsUnique_coefficients (y : V → K) :
    ∃! x : Column (b := b) (l := l) pairs → K,
      ∀ v, ∑ col, matrix color sideIndex constraint pairs good alphabet complete packing leftovers v col * x col = y v := by
  let S := synthesis color sideIndex constraint pairs good alphabet complete packing leftovers
  refine ⟨S.symm y, ?_, ?_⟩
  · intro v
    rw [matrix_mul]
    exact congrFun (S.apply_symm_apply y) v
  · intro x hx
    apply S.injective
    apply funext
    intro v
    rw [← matrix_mul, hx]
    exact (congrFun (S.apply_symm_apply y) v).symm

end SubexponentialSAT.Subexp.GlobalBasis

end OAI.Algorithms
