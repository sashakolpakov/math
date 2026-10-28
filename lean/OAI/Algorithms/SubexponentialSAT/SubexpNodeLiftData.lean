import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpWordLift
import OAI.Algorithms.SubexponentialSAT.SubexpMachineNodeOrder

namespace OAI.Algorithms

/-! # Exact word representations for lifting the generated node table

These are data and representation theorems. The record-map machine is supplied
separately; no list map in this file is counted as a machine instruction.
-/

namespace SubexponentialSAT.SubexpNodeLiftData

open SubexpLiftRing SubexpQuarticRing

def encode {B : ℕ} (a : Quad (Word B)) : List Bool :=
  a.c0.val ++ a.c1.val ++ a.c2.val ++ a.c3.val

@[simp] theorem encode_length {B : ℕ} (a : Quad (Word B)) :
    (encode a).length = 4 * B := by
  simp [encode, a.c0.property, a.c1.property, a.c2.property, a.c3.property]
  omega

theorem encode_injective {B : ℕ} (hB : 0 < B) :
    Function.Injective (encode (B := B)) := by
  let code : StackEncoding.BlockCode (Word B) :=
    ⟨B, hB, Subtype.val, Subtype.property, Subtype.val_injective⟩
  intro a b hab
  have h : [a.c0, a.c1, a.c2, a.c3] = [b.c0, b.c1, b.c2, b.c3] := by
    apply StackEncoding.encodeDataStack_injective code
    simpa [StackEncoding.encodeDataStack, code, encode, List.append_assoc] using hab
  cases a
  cases b
  simp only [List.cons.injEq, and_true] at h
  rcases h with ⟨rfl, rfl, rfl, rfl⟩
  rfl

variable (p μ : ℕ) [Fact p.Prime]

/-- Each coefficient of the actual word lift has the canonical target code. -/
theorem liftWordRun_eq_encodeWord (M : SubexpPreparedQuartic.Modulus p 1)
    (hμ : 0 < μ) (x : Word (baseWidth p 1)) :
    (SubexpWordLift.liftWordRun p μ M x).1 =
      encodeWord p μ ((SubexpWordLift.sourceValue p x).val : ZMod (p ^ μ)) := by
  apply Subtype.ext
  apply SubexpModulusConstruction.bits_eq_of_length_of_value
  · exact (SubexpWordLift.liftWordRun p μ M x).1.property.trans
      (encodeWord p μ ((SubexpWordLift.sourceValue p x).val : ZMod (p ^ μ))).property.symm
  · rw [SubexpWordLift.liftWordRun_raw p μ M hμ x]
    change _ = BinaryArithmetic.toNat (encodeBase p μ _)
    rw [encodeBase_value]
    exact (ZMod.val_natCast_of_lt
      ((ZMod.val_lt (SubexpWordLift.sourceValue p x)).trans_le (Nat.le_pow hμ))).symm

def sourceQuad (c : SubexpFieldNodes.Coefficients p) : Quad (Word (baseWidth p 1)) :=
  (SubexpFieldNodes.liftQuad p 1 c).map (encodeWord p 1)

theorem sourceQuad_value (c : SubexpFieldNodes.Coefficients p) :
    (sourceQuad p c).map (SubexpWordLift.sourceValue p) = Quad.ofFn c := by
  simp [sourceQuad, SubexpFieldNodes.liftQuad, Quad.map, Quad.ofFn,
    SubexpWordLift.sourceValue, encodeWord, encodeBase_value,
    SubexpFieldNodes.liftCoefficients_val p 1 (by decide)]

omit [Fact p.Prime] in
theorem encode_sourceQuad (c : SubexpFieldNodes.Coefficients p) :
    encode (sourceQuad p c) = SubexpFieldNodes.encodeCoefficients p c := by
  rfl

theorem encode_liftQuadRun (M : SubexpPreparedQuartic.Modulus p 1)
    (hμ : 0 < μ) (c : SubexpFieldNodes.Coefficients p) :
    encode (SubexpWordLift.liftQuadRun p μ M (sourceQuad p c)).1 =
      SubexpQuarticEncoding.encodeQuad p μ (SubexpFieldNodes.liftQuad p μ c) := by
  have hq : (SubexpWordLift.liftQuadRun p μ M (sourceQuad p c)).1 =
      (Quad.ofFn c).map (fun z : ZMod p => encodeWord p μ (z.val : ZMod (p ^ μ))) := by
    rw [← sourceQuad_value p c]
    cases sourceQuad p c
    simp [SubexpWordLift.liftQuadRun, Quad.map, liftWordRun_eq_encodeWord p μ M hμ]
  rw [hq]
  rfl

def nodeQuads : List (Quad (Word (baseWidth p 1))) :=
  List.ofFn fun i : Fin (p ^ 4 - 1) => sourceQuad p (SubexpMachineNodeOrder.nodeCoefficients p i)

theorem nodeQuads_encoded : (nodeQuads p).map encode = SubexpMachineNodeOrder.nodeWords p := by
  apply List.ext_getElem
  · simp [nodeQuads]
  · intro i hi hj
    have hip : i < p ^ 4 - 1 := by simpa [nodeQuads] using hi
    simp only [nodeQuads, List.getElem_map, List.getElem_ofFn, encode_sourceQuad]
    exact (SubexpMachineNodeOrder.node_word p ⟨i, hip⟩).symm

def liftedNodeWords (M : SubexpPreparedQuartic.Modulus p 1) : List (List Bool) :=
  (nodeQuads p).map (fun a => encode (SubexpWordLift.liftQuadRun p μ M a).1)

theorem liftedNodeWords_get (M : SubexpPreparedQuartic.Modulus p 1)
    (hμ : 0 < μ) (i : Fin (p ^ 4 - 1)) :
    (liftedNodeWords p μ M).get ⟨i.val, by simp [liftedNodeWords, nodeQuads]⟩ =
      SubexpQuarticEncoding.encodeSelected p μ hμ
        (SubexpActualRing.sectionValue p μ hμ (SubexpMachineNodeOrder.nodeEquiv p i).val) := by
  simp only [liftedNodeWords, nodeQuads, List.get_eq_getElem, List.getElem_map,
    List.getElem_ofFn, encode_liftQuadRun p μ M hμ]
  exact SubexpMachineNodeOrder.lifted_node_code p μ hμ i

@[simp] theorem liftedNodeWords_length (M : SubexpPreparedQuartic.Modulus p 1) :
    (liftedNodeWords p μ M).length = p ^ 4 - 1 := by
  simp [liftedNodeWords, nodeQuads]

end SubexponentialSAT.SubexpNodeLiftData

end OAI.Algorithms
