import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeOrder
import OAI.Algorithms.SubexponentialSAT.SubexpTupleRefinement
import OAI.Algorithms.SubexponentialSAT.SubexpNodeFilterSpec
import OAI.Algorithms.SubexponentialSAT.SubexpEnumerationPayload

namespace OAI.Algorithms

/-!
# Selected-field nodes in the tuple machine's actual output order

The raw tuples use the fixed tuple program's order. The nonzero filter prepends
retained records, so its output is the reverse of the filtered raw list. The
node equivalence below uses exactly that order.
-/

namespace SubexponentialSAT.SubexpMachineNodeOrder

open SubexpFieldNodes SubexpTupleRefinement

variable (p : ℕ) [Fact p.Prime]

theorem scalar_block (c : Coefficients p) (i : Fin 4) :
    (SubexpEnumerationPayload.scalarCode p).block (c i) =
      SubexpLiftRing.encodeBase p 1 (liftCoefficients p 1 c i) := by
  simp only [SubexpEnumerationPayload.scalarCode,
    SubexpEnumerationPayload.scalarBits, SubexpEnumerationPayload.scalarWidth,
    SubexpLiftRing.encodeBase, SubexpLiftRing.baseWidth, one_mul,
    liftCoefficients_val p 1 (by decide)]

theorem encodeTuple_scalar (c : Coefficients p) :
    encodeTuple (SubexpEnumerationPayload.scalarCode p) c = encodeCoefficients p c := by
  simp only [encodeTuple, List.ofFn_succ, List.ofFn_zero,
    StackEncoding.encodeDataStack_cons, StackEncoding.encodeDataStack_nil,
    scalar_block, encodeCoefficients, SubexpQuarticEncoding.encodeQuad,
    liftQuad, SubexpQuarticRing.Quad.ofFn, List.append_nil, List.append_assoc]
  rfl

/-- Source-level output of the fixed tuple generator at depth four. -/
def rawWords : List (List Bool) :=
  Subexp.TupleProgram.powerRows
    ((QuarticSearch.elements p).map (SubexpEnumerationPayload.scalarCode p).block) 4 [[]]

/-- The exact order produced by a prepend-emitting nonzero-record filter. -/
def nodeWords : List (List Bool) :=
  ((rawWords p).filter PositiveWordProgram.positive).reverse

theorem rawWords_perm :
    (rawWords p).Perm ((allData p).map (encodeCoefficients p)) := by
  have h := powerRows_encoded_perm (SubexpEnumerationPayload.scalarCode p)
    (QuarticSearch.elements p) 4
  have he : encodeTuple (SubexpEnumerationPayload.scalarCode p) (n := 4) =
      encodeCoefficients p := funext (encodeTuple_scalar p)
  simpa only [rawWords, allData, he] using h

@[simp] theorem rawWords_length : (rawWords p).length = p ^ 4 := by
  rw [(rawWords_perm p).length_eq, List.length_map, allData_length]

theorem rawWords_word_length (bits : List Bool) (h : bits ∈ rawWords p) :
    bits.length = 4 * (Nat.log 2 p + 1) := by
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp ((rawWords_perm p).mem_iff.mp h)
  exact encodeCoefficients_length p c

theorem nodeWords_perm : (nodeWords p).Perm (encodedFieldData p) := by
  have h := (rawWords_perm p).filter PositiveWordProgram.positive
  rw [SubexpNodeFilterSpec.filter_allData] at h
  exact (List.reverse_perm _).trans h

theorem nodeWords_nodup : (nodeWords p).Nodup :=
  (nodeWords_perm p).nodup_iff.mpr (encodedFieldData_nodup p)

@[simp] theorem nodeWords_length : (nodeWords p).length = p ^ 4 - 1 :=
  (nodeWords_perm p).length_eq.trans (encodedFieldData_length p)

theorem nodeWords_word_length (bits : List Bool) (h : bits ∈ nodeWords p) :
    bits.length = 4 * (Nat.log 2 p + 1) := by
  have hfield := (nodeWords_perm p).mem_iff.mp h
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hfield
  exact encodeCoefficients_length p c

/-- No semantic node order is substituted: the equivalence follows the
actual tuple and filter output word for word. -/
noncomputable def nodeEquiv :
    Fin (p ^ 4 - 1) ≃ {z : SubexpActualRing.E p // z ≠ 0} :=
  SubexpNodeOrder.nodeEquiv p (nodeWords p) (nodeWords_perm p)

def nodeCoefficients (i : Fin (p ^ 4 - 1)) : Coefficients p :=
  SubexpNodeOrder.nodeCoefficients p (nodeWords p) (nodeWords_perm p) i

theorem node_word (i : Fin (p ^ 4 - 1)) :
    (nodeWords p).get ⟨i.val, by rw [nodeWords_length]; exact i.isLt⟩ =
      encodeCoefficients p (nodeCoefficients p i) :=
  SubexpNodeOrder.word_at_nodeIndex p (nodeWords p) (nodeWords_perm p) i

theorem node_value (i : Fin (p ^ 4 - 1)) :
    (nodeEquiv p i).val = interpret p (nodeCoefficients p i) := rfl

/-- The coefficientwise word lift denotes the section value in the actual
machine node order as well. -/
theorem lifted_node_value (μ : ℕ) (hμ : 0 < μ) (i : Fin (p ^ 4 - 1)) :
    SubexpQuarticRing.quotientDenote (QuarticSearch.liftedCoefficients p μ)
      (liftQuad p μ (nodeCoefficients p i)) =
      SubexpActualRing.sectionValue p μ hμ (nodeEquiv p i).val := by
  rw [node_value]
  exact quotientDenote_liftQuad p μ hμ (nodeCoefficients p i)

theorem lifted_node_code (μ : ℕ) (hμ : 0 < μ) (i : Fin (p ^ 4 - 1)) :
    SubexpQuarticEncoding.encodeQuad p μ (liftQuad p μ (nodeCoefficients p i)) =
      SubexpQuarticEncoding.encodeSelected p μ hμ
        (SubexpActualRing.sectionValue p μ hμ (nodeEquiv p i).val) := by
  rw [← lifted_node_value]
  exact (SubexpQuarticEncoding.encodeQuotient_quotientDenote p μ hμ _ _).symm

end SubexponentialSAT.SubexpMachineNodeOrder

end OAI.Algorithms
