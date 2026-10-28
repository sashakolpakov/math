import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.NodeCacheBounds

namespace OAI.Algorithms

/-! Exact and polynomial byte counts for the output of the physical origin
map. This companion leaves the published cache/runtime bounds unchanged. -/
namespace SubexponentialSAT.Subexp.NodeOriginBytes

def outputBound (m C b : ℕ) : ℕ := 1+4*m+(16*b+4)*(m*C)

private theorem sum_lengths_le {A : Type*} (rows : List (List A)) (C : ℕ)
    (hC : ∀ row ∈ rows, row.length ≤ C) :
    (rows.map List.length).sum ≤ rows.length*C := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
      have hr := hC row (by simp)
      have ht := ih (fun xs hx => hC xs (by simp [hx]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith

section Bytes

variable (p : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1)
variable (width : List Bool) (hw : width.length=SubexpLiftRing.baseWidth p 1)

theorem outputBytes_length {W : ℕ} (rows : List (List (SubexpOriginControl.Row W))) :
    (SubexpOriginControl.outputBytes p M width hw rows).length =
      1+4*rows.length+(16*SubexpLiftRing.baseWidth p 1+4)*(rows.map List.length).sum :=
  SubexpOriginMap.outputBytes_length p M width hw rows

/-- The input coefficient width is unrestricted: each emitted origin uses
the source field's fixed width. -/
theorem outputBytes_le_counts {W : ℕ} (rows : List (List (SubexpOriginControl.Row W)))
    (m C b : ℕ) (hm : rows.length ≤ m)
    (hC : ∀ coordinates ∈ rows, coordinates.length ≤ C)
    (hb : SubexpLiftRing.baseWidth p 1 ≤ b) :
    (SubexpOriginControl.outputBytes p M width hw rows).length ≤ outputBound m C b := by
  have hs : (rows.map List.length).sum ≤ m*C :=
    (sum_lengths_le rows C hC).trans (Nat.mul_le_mul_right C hm)
  rw [outputBytes_length]
  unfold outputBound
  gcongr

end Bytes

theorem outputBound_le_uniform {m C b S : ℕ}
    (hm : m ≤ S) (hC : C ≤ S) (hb : b ≤ S) (hS : 1 ≤ S) :
    outputBound m C b ≤ 25*S^3 := by
  have hmono : outputBound m C b ≤ outputBound S S S := by
    unfold outputBound
    gcongr
  have heq : outputBound S S S=16*S^3+4*S^2+4*S+1 := by
    unfold outputBound
    ring
  rw [heq] at hmono
  have h0 : 1 ≤ S^3 := Nat.one_le_pow _ _ hS
  have h1 : S ≤ S^3 := by simpa using Nat.pow_le_pow_right hS (by decide : 1 ≤ 3)
  have h2 : S^2 ≤ S^3 := Nat.pow_le_pow_right hS (by decide)
  omega

theorem outputBound_le (m C R N B b modulusLen : ℕ) :
    outputBound m C b ≤ 25*(NodeCacheBounds.scale m C R N B b modulusLen)^3 := by
  apply outputBound_le_uniform <;> unfold NodeCacheBounds.scale <;> omega

/-- Bound on the actual serialized origin-map result, for direct use in
the next factor-packet input size. Instantiate `C` by the node's dimension. -/
theorem outputBytes_le (p : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1)
    (width : List Bool) (hw : width.length=SubexpLiftRing.baseWidth p 1)
    {W : ℕ} (rows : List (List (SubexpOriginControl.Row W)))
    (m C R N B b modulusLen : ℕ) (hm : rows.length ≤ m)
    (hC : ∀ coordinates ∈ rows, coordinates.length ≤ C)
    (hb : SubexpLiftRing.baseWidth p 1 ≤ b) :
    (SubexpOriginControl.outputBytes p M width hw rows).length ≤
      25*(NodeCacheBounds.scale m C R N B b modulusLen)^3 :=
  (outputBytes_le_counts p M width hw rows m C b hm hC hb).trans
    (outputBound_le m C R N B b modulusLen)

end SubexponentialSAT.Subexp.NodeOriginBytes

#print axioms SubexponentialSAT.Subexp.NodeOriginBytes.outputBytes_length
#print axioms SubexponentialSAT.Subexp.NodeOriginBytes.outputBytes_le

end OAI.Algorithms
