import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorRouting

namespace OAI.Algorithms

/-! Polynomial instruction bounds for the concrete factor router. -/

namespace SubexponentialSAT.SubexpFactorRoutingBounds

open BitProgram StructuredCalls SubexpFactorRoutingControl SubexpFactorRoutingCalls
open SubexpFactorRoutingTraversal SubexpFactorRoutingSetup

def payloadLength {r Q : ℕ} (items : List (Item r Q)) : ℕ :=
  (items.map (fun x => x.2.length)).sum

theorem encoded_length (xs : List (List Bool)) :
    (Encoding.encodeList id xs).length =
      2 * (xs.map List.length).sum + 2 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [Encoding.length_encodeList_cons, id_eq, List.map_cons,
        List.sum_cons, List.length_cons, ih]
      omega

theorem encoded_reverse_length (xs : List (List Bool)) :
    (Encoding.encodeList id xs.reverse).length = (Encoding.encodeList id xs).length := by
  simp only [encoded_length, List.map_reverse, List.sum_reverse, List.length_reverse]

theorem retained_length_le {r Q : ℕ} (t : Fin Q) (g : Fin r) (items : List (Item r Q)) :
    (Encoding.encodeList id (retained t g items)).length ≤
      (Encoding.encodeList id (items.map Prod.snd)).length := by
  induction items with
  | nil => exact le_rfl
  | cons x xs ih =>
      by_cases h : x.1 t = g
      · simpa [retained, h, Encoding.length_encodeList_cons] using
          Nat.add_le_add_left ih (2 * x.2.length + 2)
      · simpa [retained, h, Encoding.length_encodeList_cons] using
          ih.trans (Nat.le_add_left _ (2 * x.2.length + 2))

theorem budget_eq {r Q : ℕ} (W t r' g : ℕ) (items : List (Item r Q)) :
    budget W t r' g items = 11 * payloadLength items +
      items.length * (16 * W + readColorBudget t r' + 9 * g + 11 * r' + 107) + 1 := by
  induction items with
  | nil => simp [budget, payloadLength]
  | cons x xs ih =>
      simp only [budget, callbackBudget, ih, payloadLength, List.map_cons,
        List.sum_cons, List.length_cons]
      ring

theorem overhead_le {r Q : ℕ} (t : Fin Q) (g : Fin r) :
    16 * (Q * r) + readColorBudget t.val r + 9 * g.val + 11 * r + 107 ≤
      200 * (Q + 1) * (r + 1) := by
  have ht : t.val ≤ Q := t.isLt.le
  have hg : g.val ≤ r := g.isLt.le
  have htr := Nat.mul_le_mul_right r ht
  unfold readColorBudget SubexpHeadColorProgram.budget
  nlinarith

theorem budget_le {r Q : ℕ} (t : Fin Q) (g : Fin r) (items : List (Item r Q)) :
    budget (Q * r) t.val r g.val items ≤
      (Encoding.encodeList id (items.map Prod.snd)).length *
        (200 * (Q + 1) * (r + 1) + 11) + 1 := by
  let L := (Encoding.encodeList id (items.map Prod.snd)).length
  have hL : L = 2 * payloadLength items + 2 * items.length + 1 := by
    simp [L, encoded_length, payloadLength, List.map_map, Function.comp_def]
  have hp : payloadLength items ≤ L := by omega
  have hn : items.length ≤ L := by omega
  rw [budget_eq]
  calc
    _ ≤ 11 * L + L * (200 * (Q + 1) * (r + 1)) + 1 := by
      exact Nat.add_le_add_right
        (Nat.add_le_add (Nat.mul_le_mul_left 11 hp)
          (Nat.mul_le_mul hn (overhead_le t g))) 1
    _ = _ := by dsimp [L]; ring

/-- A polynomial in the physical input lengths and the color/node counts.
The padded binary color incurs its actual value-dependent conversion cost. -/
def runtimeBound (L0 L1 L2 L3 Q r : ℕ) : ℕ :=
  7 * (L0 + L1 + L2 + L3) + 32 * (r + 1) * (L2 + 1) +
    L1 * (200 * (Q + 1) * (r + 1) + 11) + 10 * L1 +
    2 * L0 + 2 * r + 2 * Q + 60

theorem runtime_le {r Q : ℕ} (t : Fin Q) (g : Fin r)
    (items : List (Item r Q)) (suffix : List Bool) (d : Data)
    (h0 : d.stacks 0 = words items ++ suffix)
    (h1 : d.stacks 1 = Encoding.encodeList id (items.map Prod.snd))
    (h2 : CounterPrograms.value (d.stacks 2) = g.val) :
    SubexpFactorRouting.runtime d t g items suffix ≤
      runtimeBound (d.stacks 0).length (d.stacks 1).length
        (d.stacks 2).length (d.stacks 3).length Q r := by
  have hloop := budget_le t g items
  rw [← h1] at hloop
  have hout := retained_length_le t g items
  rw [← h1] at hout
  have hsuffix : suffix.length ≤ (d.stacks 0).length := by
    rw [h0, List.length_append]
    omega
  have hconversion : CounterConversions.runtimeBound (d.stacks 2) ≤
      32 * (r + 1) * ((d.stacks 2).length + 1) := by
    unfold CounterConversions.runtimeBound
    rw [h2]
    exact Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left 32 (Nat.add_le_add_right g.isLt.le 1))
  have ht := t.isLt
  have hg := g.isLt
  unfold SubexpFactorRouting.runtime prepareBudget runtimeBound
  rw [encoded_reverse_length]
  omega

theorem program_runs_polynomial {r Q : ℕ} (t : Fin Q) (g : Fin r)
    (items : List (Item r Q)) (suffix : List Bool) (d : Data)
    (hc : Clean d)
    (h0 : d.stacks 0 = words items ++ suffix)
    (h1 : d.stacks 1 = Encoding.encodeList id (items.map Prod.snd))
    (h2 : CounterPrograms.value (d.stacks 2) = g.val)
    (h3 : d.stacks 3 = unary t.val) (h4 : d.stacks 4 = unary r)
    (h5 : (d.stacks 5).length = Q * r) :
    RunsIn program
      (runtimeBound (d.stacks 0).length (d.stacks 1).length
        (d.stacks 2).length (d.stacks 3).length Q r)
      (d.withPC (some program.entry))
      ((result d (Encoding.encodeList id (retained t g items))).withPC none) := by
  obtain ⟨n, hn, hrun⟩ := SubexpFactorRouting.program_runs t g items suffix d hc h0 h1 h2 h3 h4 h5
  exact ⟨n, hn.trans (runtime_le t g items suffix d h0 h1 h2), hrun⟩

end SubexponentialSAT.SubexpFactorRoutingBounds

end OAI.Algorithms
