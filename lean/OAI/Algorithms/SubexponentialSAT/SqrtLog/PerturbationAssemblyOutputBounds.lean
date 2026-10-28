import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyNativeFactor
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyBounds

namespace OAI.Algorithms

/-! Polynomial storage bounds for the actual emitted, unnormalized output. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def incidenceBitsBound (n J W : ℕ) : ℕ :=
  2*n+2*W+6+n*(J*(2*(n+J+W+4)))

theorem coordinateResult_length {B d n : ℕ} (ops : RingProgram (Coeff B d))
    (J : ℕ) (theta : Coeff B d) (v : Fin n) (P : List (Coeff B d)) (acc : List Bool) :
    (coordinateResult ops J theta v P acc).length ≤
      acc.length+J*(2*(n+J+d*B+4)) := by
  let cs := ((shiftedValue ops J theta P).val.map RingProgram.flat).tail
  have hlen : cs.length ≤ J := by simp [cs,(shiftedValue ops J theta P).property]
  have hc : ∀ c∈cs,c.length=d*B := by
    intro c hc
    have hm := List.mem_of_mem_tail hc
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hm
    exact RingProgram.flat_length x
  have h := emitted_length_bound (Squarefree.encodeMask {v}) J (d*B) cs hc 1 (by omega) acc
  change (coordinateResult ops J theta v P acc).length ≤ _ at h
  simp only [Squarefree.encodeMask_length] at h
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hlen) _)

theorem rowsResult_length {B d : ℕ} (ops : RingProgram (Coeff B d))
    (J n N : ℕ) (theta : Coeff B d) (rows : List (Fixed.Array B d N)) (j : ℕ) (acc : List Bool) :
    (rowsResult (scanStep ops J n N theta) j rows acc).length ≤
      acc.length+rows.length*(J*(2*(n+J+d*B+4))) := by
  induction rows generalizing j acc with
  | nil => simp [rowsResult]
  | cons p ps ih =>
      simp only [rowsResult]
      have h := ih (j+1) (scanStep ops J n N theta j p acc)
      have hs : (scanStep ops J n N theta j p acc).length ≤ acc.length+J*(2*(n+J+d*B+4)) := by
        unfold scanStep
        split
        · exact coordinateResult_length ops J theta _ p.val acc
        · omega
      simp only [List.length_cons]
      nlinarith

theorem sourceWords_length {B d N : ℕ} (rows : List (Fixed.Array B d N × Bool)) :
    (sourceWords rows).length=rows.length*(2*(N*(d*B))+2)+1 := by
  induction rows with
  | nil => simp [sourceWords]
  | cons row rows ih =>
      simp only [sourceWords,List.map_cons,Encoding.length_encodeList_cons,Fixed.encode_length] at *
      rw [ih]
      simp only [List.length_cons]
      ring

theorem lowOutput_length (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)) (old : List Bool) :
    (lowOutput t a M cache J N theta rows old).length ≤
      old.length+incidenceBitsBound rows.length J (d*baseWidth 3 t) := by
  have h := rowsResult_length (RingProgram.modelProgram t a M cache) J rows.length N theta
    (rows.map Prod.fst) 0
    (Encoding.frame (originKey rows.length)++Encoding.frame
      (RingProgram.flat (PerturbationBetaProgram.runValue t a M cache theta (pairedRows rows)))++old)
  change (lowOutput t a M cache J N theta rows old).length ≤ _ at h
  simp only [List.length_append,Encoding.length_frame,RingProgram.flat_length,List.length_map] at h
  have hk : (originKey rows.length).length=rows.length+2 := by
    simp [originKey,PerturbationEmitProgram.keyBits,PerturbationProgram.Key.bits]
  rw [hk] at h
  unfold incidenceBitsBound
  omega

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
