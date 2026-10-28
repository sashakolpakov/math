import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingNodeProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModelNodes
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramModel

namespace OAI.Algorithms

/-! The physical radix generator emits precisely the coefficient encoding of
nodes in the actual supplied-polynomial unramified ring. -/
namespace SubexponentialSAT.SqrtLog.RingNodeProgram

open SubexponentialSAT BinaryArithmetic SubexpLiftRing SubexpQuarticRing
open RingProgram

/-- A fixed-width coefficient encoding of a base-three index. -/
def nodeCode (t d n : ℕ) : Code (ScalarCode 3 t) d :=
  fun j => ⟨fixedBits (baseWidth 3 t) (n / 3^j.val % 3), fixedBits_length _ _⟩

theorem digits_eq_ofFn (B p d n : ℕ) :
    digits B p d n =
      (List.ofFn fun j : Fin d => fixedBits B (n / p^j.val % p)).flatten := by
  induction d generalizing n with
  | zero => simp [digits]
  | succ d ih =>
    simp only [digits, List.ofFn_succ, List.flatten_cons, Fin.val_zero, pow_zero,
      Nat.div_one, Fin.val_succ]
    rw [ih]
    simp_rw [pow_succ', Nat.div_div_eq_div_mul]

theorem nodeCode_flat (t d n : ℕ) :
    flat (nodeCode t d n) = digits (baseWidth 3 t) 3 d n :=
  (digits_eq_ofFn _ _ _ _).symm

theorem nodeCode_value (t d n : ℕ) (ht : 0 < t) (j : Fin d) :
    BinaryArithmetic.toNat (nodeCode t d n j).val = n / 3^j.val % 3 := by
  apply toNat_fixedBits_of_lt
  have hc : 2^2 ≤ 2^(2*t) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [ternary_baseWidth]
  have hm := Nat.mod_lt (n / 3^j.val) (by decide : 0 < 3)
  norm_num at hc
  omega

theorem nodeCode_canonical (t d n : ℕ) (ht : 0 < t) (j : Fin d) :
    BinaryArithmetic.toNat (nodeCode t d n j).val < 3^t := by
  rw [nodeCode_value t d n ht]
  exact (Nat.mod_lt _ (by decide)).trans_le (by
    simpa using (Nat.pow_le_pow_right (by decide : 1 ≤ 3) ht : 3^1 ≤ 3^t))

theorem residueNode_coordinate {d : ℕ} (a : RingModel.Data d) (Q : ℕ)
    (hQ : Q < 3^d) (i : Fin Q) (j : Fin d) :
    (a.fieldCoordinates (a.residueNode Q hQ i) j).val = (i.val+1) / 3^j.val % 3 := by
  let index : Fin (3^d) := ⟨i.val+1, by omega⟩
  let v : Fin d → ZMod 3 := fun j =>
    ZMod.finEquiv 3 ((finFunctionFinEquiv.symm index) j)
  change (a.fieldCoordinates (a.fieldCoordinates.symm v) j).val = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The physical words decode to the same nodes used by interpolation. -/
theorem nodeCode_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) (Q : ℕ) (hQ : Q < 3^d) (i : Fin Q) :
    (modelRing t ht hd a M cache).decode (nodeCode t d (i.val+1)) =
      a.node t Q ht hQ i := by
  rw [modelRing_decode]
  unfold RingModel.Data.node RingModel.Data.sectionValue
  congr 1
  funext j
  unfold wordValue
  rw [nodeCode_value t d (i.val+1) ht j, residueNode_coordinate]

theorem stream_eq_flat_nodes (t d Q : ℕ) :
    stream (baseWidth 3 t) 3 d Q =
      (List.finRange Q).flatMap (fun i => flat (nodeCode t d (i.val+1))) := by
  induction Q with
  | zero => simp [stream]
  | succ Q ih =>
    rw [stream, List.finRange_succ_last, List.flatMap_append, List.flatMap_map,
      List.flatMap_singleton, ih]
    simp only [ Fin.val_castSucc, Fin.val_last, nodeCode_flat]

/-- Public one-row hook for callers which frame or process each generated
node before continuing their own loop. Both input masters are preserved. -/
theorem row_command_eval (r : Fin 8 → Bool) (t : ℕ)
    (m rank arity : List Bool) (hm : BinaryArithmetic.toNat m = 3) (hw : m.length = baseWidth 3 t) :
    ∃ n ≤ SubexpFieldRowPreparation.budget m rank arity, ∃ rf,
      StructuredCalls.Eval SubexpFieldRowPreparation.command n
        (SubexpFieldRowPreparation.data r m rank arity [] [] [])
        (SubexpFieldRowPreparation.data rf m rank arity [] []
          (flat (nodeCode t arity.length (BinaryArithmetic.toNat rank)))) := by
  obtain ⟨n,hn,rf,he⟩ := SubexpFieldRowPreparation.command_eval r m rank arity []
  rw [unrank_eq_digits m rank (by omega), hm, hw, List.append_nil,
    ← nodeCode_flat] at he
  exact ⟨n,hn,rf,he⟩

/-- The generated nodes have pairwise distinct, nonzero residues. -/
theorem generated_residue_injective (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) (Q : ℕ) (hQ : Q < 3^d) :
    Function.Injective (fun i : Fin Q => a.rho t ht
      ((modelRing t ht hd a M cache).decode (nodeCode t d (i.val+1)))) := by
  simp_rw [nodeCode_decode t ht hd a M cache Q hQ, RingModel.Data.rho_node]
  exact a.residueNode_injective Q hQ

theorem generated_residue_ne_zero (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) (Q : ℕ) (hQ : Q < 3^d) (i : Fin Q) :
    a.rho t ht ((modelRing t ht hd a M cache).decode (nodeCode t d (i.val+1))) ≠ 0 := by
  rw [nodeCode_decode t ht hd a M cache Q hQ, RingModel.Data.rho_node]
  exact a.residueNode_ne_zero Q hQ i

end SubexponentialSAT.SqrtLog.RingNodeProgram

end OAI.Algorithms
