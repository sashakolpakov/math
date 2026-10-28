import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeMask
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeSupportCount

namespace OAI.Algorithms

/-! Pruned enumeration of bounded-weight Boolean masks. Every recursive call
extends an admissible prefix; there is no enumeration of all binary words. -/
namespace SubexponentialSAT.SqrtLog.SupportProgram

/-- Enumerate the length-n masks with strictly fewer than J set bits. -/
def masks : ℕ → ℕ → List (List Bool)
  | _, 0 => []
  | 0, _ + 1 => [[]]
  | n + 1, J + 1 =>
      (masks n (J + 1)).map (false :: ·) ++ (masks n J).map (true :: ·)

@[simp] theorem masks_zero_bound (n : ℕ) : masks n 0 = [] := by cases n <;> rfl

@[simp] theorem mem_masks (n J : ℕ) (xs : List Bool) :
    xs ∈ masks n J ↔ xs.length = n ∧ xs.count true < J := by
  induction n generalizing J xs with
  | zero =>
      cases J with
      | zero => simp [masks]
      | succ J => cases xs <;> simp [masks]
  | succ n ih =>
      cases J with
      | zero => simp [masks]
      | succ J =>
          cases xs with
          | nil => simp [masks]
          | cons b xs =>
              cases b <;> simp [masks, ih ]

theorem masks_nodup (n J : ℕ) : (masks n J).Nodup := by
  induction n generalizing J with
  | zero => cases J <;> simp [masks]
  | succ n ih =>
      cases J with
      | zero => simp [masks]
      | succ J =>
          rw [masks, List.nodup_append]
          refine ⟨?_, ?_, ?_⟩
          · exact (ih (J + 1)).map (by intro a b h; exact List.cons.inj h |>.2)
          · exact (ih J).map (by intro a b h; exact List.cons.inj h |>.2)
          · intro xs hx ys hys hxy
            obtain ⟨a, _, ha⟩ := List.mem_map.mp hx
            obtain ⟨b, _, hb⟩ := List.mem_map.mp hys
            have h := ha.trans (hxy.trans hb.symm)
            cases h

/-- Count of recursive calls in the explicit pruned recursive specification. -/
def calls : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 1
  | n + 1, J + 1 => 1 + calls n (J + 1) + calls n J

@[simp] theorem calls_zero_bound (n : ℕ) : calls n 0 = 1 := by cases n <;> rfl

/-- The enumeration tree has only polynomially many nodes per emitted mask. -/
theorem calls_le (n J : ℕ) (hJ : 0 < J) :
    calls n J ≤ (2 * n + 1) * (masks n J).length := by
  induction n generalizing J with
  | zero => cases J <;> simp_all [calls, masks]
  | succ n ih =>
      cases J with
      | zero => omega
      | succ J =>
          have hleft := ih (J + 1) (Nat.succ_pos J)
          have hne : 0 < (masks n (J + 1)).length := by
            have hm : List.replicate n false ∈ masks n (J + 1) := by simp [List.count_replicate]
            exact List.length_pos_iff.mpr (by intro h; simp [h] at hm)
          cases J with
          | zero =>
              simp only [calls, masks, masks_zero_bound, calls_zero_bound,
                List.map_nil, List.append_nil, List.length_map]
              nlinarith
          | succ J =>
              have hright := ih (J + 1) (Nat.succ_pos J)
              simp only [calls, masks, List.length_append, List.length_map]
              nlinarith

end SubexponentialSAT.SqrtLog.SupportProgram

end OAI.Algorithms
