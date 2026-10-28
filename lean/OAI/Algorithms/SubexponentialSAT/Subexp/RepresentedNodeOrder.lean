import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMachineNodeOrder
import OAI.Algorithms.SubexponentialSAT.SubexpSelectedConversions

namespace OAI.Algorithms

/-!
# Code words for the actual generated node order

The four source words come from the concrete coefficient tuples used by the
tuple/filter node generator. No coordinates are extracted from an abstract
field element. These are representation theorems; physical node generation
is provided separately by `SubexpNodeGeneration`.
-/

namespace SubexponentialSAT.Subexp.RepresentedNodeOrder

open SubexpSymbolicCost SubexpQuarticRing SubexpSelectedConversions

variable (p : ℕ) [Fact p.Prime]

/-- Four explicitly encoded prime-field coefficients in machine node order. -/
def nodeCode (i : Fin (p ^ 4 - 1)) : QuarticCode p 0 :=
  (Quad.ofFn (SubexpMachineNodeOrder.nodeCoefficients p i)).map labelWord

theorem nodeCode_decode (source : Prepared p 0) (i : Fin (p ^ 4 - 1)) :
    source.residueRing.decode (nodeCode p i) =
      (SubexpMachineNodeOrder.nodeEquiv p i).val := by
  rw [Prepared.residueRing_decode, SubexpMachineNodeOrder.node_value]
  change @Eq (LiftRing.Extension (QuarticSearch.poly (QuarticSearch.coefficients p))) _ _
  simpa [nodeCode, Quad.map, Quad.ofFn] using
    SubexpFieldNodes.quotientDenote_ofFn p (SubexpMachineNodeOrder.nodeCoefficients p i)

/-- The concrete source payload is precisely the word produced by the
tuple generator and nonzero-record filter at this index. -/
theorem nodeCode_bytes (i : Fin (p ^ 4 - 1)) :
    (quarticCodeBlockCode p 0).block (nodeCode p i) =
      (SubexpMachineNodeOrder.nodeWords p).get
        ⟨i.val, by rw [SubexpMachineNodeOrder.nodeWords_length]; exact i.isLt⟩ := by
  rw [SubexpMachineNodeOrder.node_word]
  simp [nodeCode, quarticCodeBlockCode, wordBlockCode, recordBlockCode,
    quadToPair, Quad.map, Quad.ofFn, labelWord, encodeWord,
    SubexpFieldNodes.encodeCoefficients, SubexpQuarticEncoding.encodeQuad,
    SubexpFieldNodes.liftQuad, SubexpFieldNodes.liftCoefficients,
    List.append_assoc]

theorem betaLift_nodeCode_decode {D : ℕ} (source : Prepared p 0)
    (target : Prepared p D) (i : Fin (p ^ 4 - 1)) :
    target.ring.decode (betaLift source D (nodeCode p i)) =
      SubexpActualRing.sectionValue p (D + 1) (Nat.succ_pos D)
        (SubexpMachineNodeOrder.nodeEquiv p i).val := by
  rw [betaLift_decode, nodeCode_decode]
  rfl

/-- Change only the finite index size; the machine node order is preserved. -/
def nodeCodeFor {Q : ℕ} (hQ : Q = p ^ 4 - 1) (i : Fin Q) : QuarticCode p 0 :=
  nodeCode p (Fin.cast hQ i)

noncomputable def nodesFor {Q : ℕ} (hQ : Q = p ^ 4 - 1) :
    Fin Q ≃ {z : SubexpActualRing.E p // z ≠ 0} :=
  (finCongr hQ).trans (SubexpMachineNodeOrder.nodeEquiv p)

theorem nodeCodeFor_decode {Q : ℕ} (hQ : Q = p ^ 4 - 1)
    (source : Prepared p 0) (i : Fin Q) :
    source.residueRing.decode (nodeCodeFor p hQ i) = (nodesFor p hQ i).val :=
  nodeCode_decode p source (Fin.cast hQ i)

theorem betaLift_nodeCodeFor_decode {Q D : ℕ} (hQ : Q = p ^ 4 - 1)
    (source : Prepared p 0) (target : Prepared p D) (i : Fin Q) :
    target.ring.decode (betaLift source D (nodeCodeFor p hQ i)) =
      SubexpActualRing.sectionValue p (D + 1) (Nat.succ_pos D) (nodesFor p hQ i).val :=
  betaLift_nodeCode_decode p source target (Fin.cast hQ i)

end SubexponentialSAT.Subexp.RepresentedNodeOrder

end OAI.Algorithms
