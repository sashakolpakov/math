import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpActualRing
import OAI.Algorithms.SubexponentialSAT.SubexpVectorEnumeration
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticEncoding

namespace OAI.Algorithms

/-!
# Executable nonzero nodes for the selected quartic field

The execution data are four coefficients. The list order is the explicit
QuarticSearch vector order, with exactly the zero vector filtered out.
Abstract field values occur only in the mathematical interpretation.
-/

namespace SubexponentialSAT.SubexpFieldNodes

abbrev Coefficients (p : ℕ) := Fin 4 → ZMod p

/-- Enumerate all coefficient vectors in explicit recursive list order. -/
def allData (p : ℕ) : List (Coefficients p) :=
  QuarticSearch.vectors (QuarticSearch.elements p) 4

/-- The actual executable node list, with the zero coefficient vector removed. -/
def nodeData (p : ℕ) : List (Coefficients p) :=
  (allData p).filter (fun c => decide (c ≠ 0))

theorem allData_length (p : ℕ) : (allData p).length = p ^ 4 := by
  simp only [allData, QuarticSearch.length_vectors, QuarticSearch.length_elements]

theorem allData_nodup (p : ℕ) : (allData p).Nodup :=
  SubexpVectorEnumeration.vectors_nodup (QuarticSearch.elements p)
    (SubexpVectorEnumeration.elements_nodup p) 4

theorem nodeData_nodup (p : ℕ) : (nodeData p).Nodup :=
  (allData_nodup p).filter _

theorem mem_allData (p : ℕ) [Fact p.Prime] (c : Coefficients p) :
    c ∈ allData p :=
  QuarticSearch.mem_vectors (QuarticSearch.elements p) (QuarticSearch.mem_elements p) 4 c

@[simp] theorem mem_nodeData (p : ℕ) [Fact p.Prime] (c : Coefficients p) :
    c ∈ nodeData p ↔ c ≠ 0 := by
  simp only [nodeData, List.mem_filter, decide_eq_true_eq]
  exact and_iff_right (mem_allData p c)

theorem nodeData_toFinset (p : ℕ) [Fact p.Prime] :
    (nodeData p).toFinset = Finset.univ.erase (0 : Coefficients p) := by
  ext c
  simp only [List.mem_toFinset, mem_nodeData, Finset.mem_erase, Finset.mem_univ,
    and_true]

/-- Every nonzero vector occurs once, so there are exactly p^4 - 1 nodes. -/
theorem nodeData_length (p : ℕ) [Fact p.Prime] :
    (nodeData p).length = p ^ 4 - 1 := by
  rw [← List.toFinset_card_of_nodup (nodeData_nodup p), nodeData_toFinset,
    Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card]

/-- Index the actual list. Both directions are executable: the inverse
searches this same list with idxOf. No arbitrary finite enumeration is used. -/
def coefficientNodeEquiv (p : ℕ) [Fact p.Prime] :
    Fin (p ^ 4 - 1) ≃ {c : Coefficients p // c ≠ 0} :=
  (finCongr (nodeData_length p).symm).trans
    ((List.Nodup.getEquiv (nodeData p) (nodeData_nodup p)).trans
      (Equiv.subtypeEquivRight (fun c => mem_nodeData p c)))

/-- Executable coefficient data of the node at a given list index. -/
def nodeCoefficients (p : ℕ) [Fact p.Prime] (i : Fin (p ^ 4 - 1)) : Coefficients p :=
  (coefficientNodeEquiv p i).val

theorem nodeCoefficients_eq_get (p : ℕ) [Fact p.Prime] (i : Fin (p ^ 4 - 1)) :
    nodeCoefficients p i =
      (nodeData p).get ⟨i.val, by rw [nodeData_length p]; exact i.isLt⟩ := by
  rfl

theorem nodeCoefficients_ne_zero (p : ℕ) [Fact p.Prime] (i : Fin (p ^ 4 - 1)) :
    nodeCoefficients p i ≠ 0 :=
  (coefficientNodeEquiv p i).property

theorem nodeCoefficients_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (nodeCoefficients p) := by
  intro i j hij
  exact (coefficientNodeEquiv p).injective (Subtype.ext hij)

theorem nodeCoefficients_complete (p : ℕ) [Fact p.Prime]
    (c : Coefficients p) (hc : c ≠ 0) :
    ∃ i, nodeCoefficients p i = c := by
  obtain ⟨i, hi⟩ := (coefficientNodeEquiv p).surjective ⟨c, hc⟩
  exact ⟨i, congrArg Subtype.val hi⟩

/-- Filtering with an actual counter for the number of zero-vector tests.
This counts predicate invocations, not machine instructions or bit time. -/
def filterWithCount (p : ℕ) : List (Coefficients p) → List (Coefficients p) × ℕ
  | [] => ([], 0)
  | c :: cs =>
    let rest := filterWithCount p cs
    (if c ≠ 0 then c :: rest.1 else rest.1, rest.2 + 1)

theorem filterWithCount_data (p : ℕ) (cs : List (Coefficients p)) :
    (filterWithCount p cs).1 = cs.filter (fun c => decide (c ≠ 0)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases hc : c ≠ 0 <;> simp [filterWithCount, hc, ih]

theorem filterWithCount_tests (p : ℕ) (cs : List (Coefficients p)) :
    (filterWithCount p cs).2 = cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [filterWithCount, ih, List.length_cons]

/-- Executable enumeration together with the exact zero-test count. -/
def enumerateNodes (p : ℕ) : List (Coefficients p) × ℕ :=
  filterWithCount p (allData p)

@[simp] theorem enumerateNodes_data (p : ℕ) :
    (enumerateNodes p).1 = nodeData p :=
  filterWithCount_data p (allData p)

@[simp] theorem enumerateNodes_tests (p : ℕ) :
    (enumerateNodes p).2 = p ^ 4 := by
  rw [enumerateNodes, filterWithCount_tests, allData_length]

section Interpretation

variable (p : ℕ) [Fact p.Prime]

/-- Proof interpretation of four coefficient words in the selected field. -/
noncomputable def interpret (c : Coefficients p) : SubexpActualRing.E p :=
  (SubexpActualRing.fieldCoordinates p).symm c

theorem interpret_injective : Function.Injective (interpret p) :=
  (SubexpActualRing.fieldCoordinates p).symm.injective

@[simp] theorem interpret_zero : interpret p 0 = 0 :=
  (SubexpActualRing.fieldCoordinates p).symm.map_zero

@[simp] theorem interpret_eq_zero_iff (c : Coefficients p) :
    interpret p c = 0 ↔ c = 0 := by
  rw [← interpret_zero p]
  exact (interpret_injective p).eq_iff

/-- Coefficient vectors and abstract field elements have the same nonzero
test; this equivalence is only used to prove the node specification. -/
noncomputable def nonzeroInterpretation :
    {c : Coefficients p // c ≠ 0} ≃ {z : SubexpActualRing.E p // z ≠ 0} where
  toFun c := ⟨interpret p c.val, (interpret_eq_zero_iff p c.val).not.mpr c.property⟩
  invFun z := ⟨SubexpActualRing.fieldCoordinates p z.val, by
    intro hz
    apply z.property
    apply (SubexpActualRing.fieldCoordinates p).injective
    rw [hz, map_zero]⟩
  left_inv c := by
    apply Subtype.ext
    exact (SubexpActualRing.fieldCoordinates p).apply_symm_apply c.val
  right_inv z := by
    apply Subtype.ext
    exact (SubexpActualRing.fieldCoordinates p).symm_apply_apply z.val

/-- The layout's node equivalence in the executable list order.
It does not refer to the earlier semantic arbitrary enumeration. -/
noncomputable def nodeEquiv :
    Fin (p ^ 4 - 1) ≃ {z : SubexpActualRing.E p // z ≠ 0} :=
  (coefficientNodeEquiv p).trans (nonzeroInterpretation p)

noncomputable def node (i : Fin (p ^ 4 - 1)) : SubexpActualRing.E p :=
  interpret p (nodeCoefficients p i)

@[simp] theorem nodeEquiv_val (i : Fin (p ^ 4 - 1)) :
    (nodeEquiv p i).val = node p i := rfl

theorem node_ne_zero (i : Fin (p ^ 4 - 1)) : node p i ≠ 0 :=
  (nodeEquiv p i).property

theorem node_injective : Function.Injective (node p) :=
  (interpret_injective p).comp (nodeCoefficients_injective p)

theorem node_complete (z : SubexpActualRing.E p) (hz : z ≠ 0) :
    ∃ i, node p i = z := by
  obtain ⟨i, hi⟩ := (nodeEquiv p).surjective ⟨z, hz⟩
  exact ⟨i, congrArg Subtype.val hi⟩

/-- Distinct executable node data interpret as distinct field elements. -/
theorem interpretedData_nodup : ((nodeData p).map (interpret p)).Nodup :=
  (nodeData_nodup p).map (interpret_injective p)

end Interpretation

section EncodedData

open SubexpQuarticRing

variable (p : ℕ) [Fact p.Prime]

/-- Four residue coefficients, stored without constructing an abstract field value. -/
def nodeQuad (i : Fin (p ^ 4 - 1)) : Quad (ZMod p) :=
  Quad.ofFn (nodeCoefficients p i)

/-- Lift the four standard integer representatives into the prime-power base. -/
def liftCoefficients (μ : ℕ) (c : Coefficients p) : Fin 4 → ZMod (p ^ μ) :=
  fun i => ((c i).val : ZMod (p ^ μ))

/-- Lifting retains each coefficient's integer value without reduction. -/
@[simp] theorem liftCoefficients_val (μ : ℕ) (hμ : 0 < μ)
    (c : Coefficients p) (i : Fin 4) :
    (liftCoefficients p μ c i).val = (c i).val :=
  ZMod.val_natCast_of_lt ((c i).val_lt.trans_le (Nat.le_pow hμ))

theorem liftCoefficients_injective (μ : ℕ) (hμ : 0 < μ) :
    Function.Injective (liftCoefficients p μ) := by
  intro a b hab
  funext i
  have hval := congrArg (fun c => (c i).val) hab
  change (liftCoefficients p μ a i).val = (liftCoefficients p μ b i).val at hval
  rw [liftCoefficients_val p μ hμ, liftCoefficients_val p μ hμ] at hval
  exact ZMod.val_injective p hval

/-- The executable record implementing the coefficientwise residue section. -/
def liftQuad (μ : ℕ) (c : Coefficients p) : Quad (ZMod (p ^ μ)) :=
  Quad.ofFn (liftCoefficients p μ c)

theorem liftQuad_injective (μ : ℕ) (hμ : 0 < μ) :
    Function.Injective (liftQuad p μ) :=
  (SubexpQuarticEncoding.quadEquiv _).symm.injective.comp
    (liftCoefficients_injective p μ hμ)

def liftedNodeQuad (μ : ℕ) (i : Fin (p ^ 4 - 1)) : Quad (ZMod (p ^ μ)) :=
  liftQuad p μ (nodeCoefficients p i)

theorem fieldCoordinates_quotientDenote (a : Quad (ZMod p)) :
    SubexpActualRing.fieldCoordinates p
      (quotientDenote (QuarticSearch.coefficients p) a) = Quad.toFn a := by
  funext i
  rw [SubexpActualRing.fieldCoordinates_apply p
    (quotientDenote (QuarticSearch.coefficients p) a) i]
  change (LiftRing.remainder (QuarticSearch.poly_monic (QuarticSearch.coefficients p))
    (quotientDenote (QuarticSearch.coefficients p) a)).coeff i = _
  rw [← SubexpQuarticEncoding.quotientCoefficients_toFn,
    SubexpQuarticEncoding.quotientCoefficients_quotientDenote]

theorem quotientDenote_ofFn (c : Coefficients p) :
    quotientDenote (QuarticSearch.coefficients p) (Quad.ofFn c) = interpret p c := by
  apply (SubexpActualRing.fieldCoordinates p).injective
  rw [fieldCoordinates_quotientDenote]
  change Quad.toFn (Quad.ofFn c) =
    (SubexpActualRing.fieldCoordinates p) ((SubexpActualRing.fieldCoordinates p).symm c)
  rw [LinearEquiv.apply_symm_apply]
  exact (SubexpQuarticEncoding.quadEquiv _).apply_symm_apply c

/-- The executable node record denotes the node in the layout's list order. -/
theorem quotientDenote_nodeQuad (i : Fin (p ^ 4 - 1)) :
    quotientDenote (QuarticSearch.coefficients p) (nodeQuad p i) = node p i :=
  quotientDenote_ofFn p (nodeCoefficients p i)

theorem ringCoordinates_quotientDenote (μ : ℕ) (hμ : 0 < μ)
    (a : Quad (ZMod (p ^ μ))) :
    SubexpActualRing.ringCoordinates p μ hμ
      (quotientDenote (QuarticSearch.liftedCoefficients p μ) a) = Quad.toFn a := by
  let _ : Fact (1 < p ^ μ) := ⟨SubexpActualRing.modulus_gt_one p μ hμ⟩
  funext i
  rw [SubexpActualRing.ringCoordinates_apply p μ hμ
    (quotientDenote (QuarticSearch.liftedCoefficients p μ) a) i]
  change (LiftRing.remainder
    (QuarticSearch.poly_monic (QuarticSearch.liftedCoefficients p μ))
    (quotientDenote (QuarticSearch.liftedCoefficients p μ) a)).coeff i = _
  rw [← SubexpQuarticEncoding.quotientCoefficients_toFn,
    SubexpQuarticEncoding.quotientCoefficients_quotientDenote]

/-- Coefficientwise lifting of an input record realizes the semantic section. -/
theorem quotientDenote_liftQuad (μ : ℕ) (hμ : 0 < μ) (c : Coefficients p) :
    quotientDenote (QuarticSearch.liftedCoefficients p μ) (liftQuad p μ c) =
      SubexpActualRing.sectionValue p μ hμ (interpret p c) := by
  apply (SubexpActualRing.ringCoordinates p μ hμ).injective
  rw [ringCoordinates_quotientDenote]
  simp only [SubexpActualRing.sectionValue, LinearEquiv.apply_symm_apply]
  change Quad.toFn (Quad.ofFn (liftCoefficients p μ c)) = _
  rw [show Quad.toFn (Quad.ofFn (liftCoefficients p μ c)) = liftCoefficients p μ c from
    (SubexpQuarticEncoding.quadEquiv _).apply_symm_apply _]
  simp only [ interpret, LinearEquiv.apply_symm_apply]
  rfl

/-- This is the node-lift refinement used by the explicit lifted layout. -/
theorem quotientDenote_liftedNodeQuad (μ : ℕ) (hμ : 0 < μ)
    (i : Fin (p ^ 4 - 1)) :
    quotientDenote (QuarticSearch.liftedCoefficients p μ) (liftedNodeQuad p μ i) =
      SubexpActualRing.sectionValue p μ hμ (node p i) :=
  quotientDenote_liftQuad p μ hμ (nodeCoefficients p i)

/-- The complete array of lifted records preserves the explicit node-list order. -/
def liftedNodeData (μ : ℕ) : List (Quad (ZMod (p ^ μ))) :=
  (nodeData p).map (liftQuad p μ)

/-- Each entry is four fixed-width binary coefficient words. -/
def encodedNodeData (μ : ℕ) : List (List Bool) :=
  (liftedNodeData p μ).map (SubexpQuarticEncoding.encodeQuad p μ)

def encodedNode (μ : ℕ) (i : Fin (p ^ 4 - 1)) : List Bool :=
  SubexpQuarticEncoding.encodeQuad p μ (liftedNodeQuad p μ i)

@[simp] theorem liftedNodeData_length (μ : ℕ) :
    (liftedNodeData p μ).length = p ^ 4 - 1 := by
  simp only [liftedNodeData, List.length_map, nodeData_length]

@[simp] theorem encodedNodeData_length (μ : ℕ) :
    (encodedNodeData p μ).length = p ^ 4 - 1 := by
  simp only [encodedNodeData, List.length_map, liftedNodeData_length]

@[simp] theorem encodedNode_length (μ : ℕ) (i : Fin (p ^ 4 - 1)) :
    (encodedNode p μ i).length = 4 * μ * (Nat.log 2 p + 1) :=
  SubexpQuarticEncoding.encodeQuad_length p μ _

theorem encodedNodeData_get (μ : ℕ) (i : Fin (p ^ 4 - 1)) :
    (encodedNodeData p μ).get
      ⟨i.val, by rw [encodedNodeData_length]; exact i.isLt⟩ = encodedNode p μ i := by
  simp only [encodedNodeData, liftedNodeData, List.get_eq_getElem, List.getElem_map,
    encodedNode, liftedNodeQuad, nodeCoefficients_eq_get]

/-- Encoding a generated record is exactly the canonical encoding of its
interpreted section value. The executable side performs no quotient extraction. -/
theorem encodedNode_eq_encodeSelected (μ : ℕ) (hμ : 0 < μ)
    (i : Fin (p ^ 4 - 1)) :
    encodedNode p μ i = SubexpQuarticEncoding.encodeSelected p μ hμ
      (SubexpActualRing.sectionValue p μ hμ (node p i)) := by
  rw [← quotientDenote_liftedNodeQuad]
  exact (SubexpQuarticEncoding.encodeQuotient_quotientDenote p μ hμ _ _).symm

omit [Fact (Nat.Prime p)] in
theorem encodedNodeData_entry_length (μ : ℕ) (b : List Bool)
    (hb : b ∈ encodedNodeData p μ) :
    b.length = 4 * μ * (Nat.log 2 p + 1) := by
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb
  exact SubexpQuarticEncoding.encodeQuad_length p μ a

theorem liftedNodeData_nodup (μ : ℕ) (hμ : 0 < μ) :
    (liftedNodeData p μ).Nodup :=
  (nodeData_nodup p).map (liftQuad_injective p μ hμ)

theorem encodedNodeData_nodup (μ : ℕ) (hμ : 0 < μ) :
    (encodedNodeData p μ).Nodup :=
  (liftedNodeData_nodup p μ hμ).map
    (SubexpQuarticEncoding.encodeQuad_injective p μ hμ)

/-- A contiguous, executable output tape containing the entire lifted-node table. -/
def encodedNodeTape (μ : ℕ) : List Bool := (encodedNodeData p μ).flatten

@[simp] theorem encodedNodeTape_length (μ : ℕ) :
    (encodedNodeTape p μ).length =
      (p ^ 4 - 1) * (4 * μ * (Nat.log 2 p + 1)) := by
  rw [encodedNodeTape, List.length_flatten]
  rw [List.map_eq_replicate_iff.mpr (encodedNodeData_entry_length p μ)]
  rw [List.sum_replicate_nat, encodedNodeData_length]

/-- An actual random-access array, in the same explicitly generated order. -/
def encodedNodeArray (μ : ℕ) : Array (List Bool) := (encodedNodeData p μ).toArray

@[simp] theorem encodedNodeArray_size (μ : ℕ) :
    (encodedNodeArray p μ).size = p ^ 4 - 1 := by
  simp only [encodedNodeArray, List.size_toArray, encodedNodeData_length]

theorem encodedNodeArray_get (μ : ℕ) (i : Fin (p ^ 4 - 1)) :
    (encodedNodeArray p μ)[i.val]'(by rw [encodedNodeArray_size]; exact i.isLt) =
      encodedNode p μ i :=
  encodedNodeData_get p μ i

/-- Residue-field coefficient encoding uses the same four words at exponent one. -/
def encodeCoefficients (c : Coefficients p) : List Bool :=
  SubexpQuarticEncoding.encodeQuad p 1 (liftQuad p 1 c)

omit [Fact (Nat.Prime p)] in
@[simp] theorem encodeCoefficients_length (c : Coefficients p) :
    (encodeCoefficients p c).length = 4 * (Nat.log 2 p + 1) := by
  simpa only [encodeCoefficients, mul_one] using
    SubexpQuarticEncoding.encodeQuad_length p 1 (liftQuad p 1 c)

theorem encodeCoefficients_injective : Function.Injective (encodeCoefficients p) :=
  (SubexpQuarticEncoding.encodeQuad_injective p 1 (by decide)).comp
    (liftQuad_injective p 1 (by decide))

/-- The residue-field table is produced directly from its coefficient vectors. -/
def encodedFieldData : List (List Bool) := (nodeData p).map (encodeCoefficients p)

omit [Fact (Nat.Prime p)] in
theorem encodedFieldData_eq : encodedFieldData p = encodedNodeData p 1 := by
  simp only [encodedFieldData, encodedNodeData, liftedNodeData, List.map_map, Function.comp_def]
  rfl

@[simp] theorem encodedFieldData_length :
    (encodedFieldData p).length = p ^ 4 - 1 := by
  simp only [encodedFieldData, List.length_map, nodeData_length]

theorem encodedFieldData_nodup : (encodedFieldData p).Nodup :=
  (nodeData_nodup p).map (encodeCoefficients_injective p)

theorem encodedFieldData_get (i : Fin (p ^ 4 - 1)) :
    (encodedFieldData p).get
      ⟨i.val, by rw [encodedFieldData_length]; exact i.isLt⟩ =
      encodeCoefficients p (nodeCoefficients p i) := by
  simp only [encodedFieldData, List.get_eq_getElem, List.getElem_map,
    nodeCoefficients_eq_get]

end EncodedData

end SubexponentialSAT.SubexpFieldNodes

end OAI.Algorithms
