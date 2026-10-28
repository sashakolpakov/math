import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorArithmetic
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram

/-! The original concrete factor accumulator, with empty correction support.
All three tape moves and the original sparse product call are charged. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram MomentsProgram

def byteBound (n B d u J : ℕ) : ℕ :=
  u * J * (2 * (u + J + n) + 2 * (d * B) + 2)

def budget (n B d u J : ℕ) : ℕ :=
  56 * byteBound n B d u J + TruncatedRingProgram.productBudget n B d u J + 54

/-- The degree and constant are fixed independently of all input dimensions. -/
theorem budget_polynomial (n B d u J : ℕ) :
    budget n B d u J ≤ 4000000 * (n + B + d + u + J + 1) ^ 10 := by
  let a := n + B + d + u + J + 1
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hn : n ≤ a := by dsimp [a]; omega
  have hB : B ≤ a := by dsimp [a]; omega
  have hd : d ≤ a := by dsimp [a]; omega
  have hu : u ≤ a := by dsimp [a]; omega
  have hJ : J ≤ a := by dsimp [a]; omega
  have hm : byteBound n B d u J ≤ byteBound a a a a a := by
    dsimp only [byteBound]
    gcongr
  have hdiag : byteBound a a a a a = 2 * a ^ 4 + 6 * a ^ 3 + 2 * a ^ 2 := by
    unfold byteBound
    ring
  have h2 : a ^ 2 ≤ a ^ 10 := Nat.pow_le_pow_right ha (by decide)
  have h3 : a ^ 3 ≤ a ^ 10 := Nat.pow_le_pow_right ha (by decide)
  have h4 : a ^ 4 ≤ a ^ 10 := Nat.pow_le_pow_right ha (by decide)
  have h0 : 1 ≤ a ^ 10 := Nat.one_le_pow 10 a ha
  rw [hdiag] at hm
  have hp := (TruncatedRingProgram.productBudget_le_local n B d u J 0).trans
    (TruncatedRingProgram.localBudget_le n B d u J 0)
  simp only [Nat.add_zero] at hp
  change TruncatedRingProgram.productBudget n B d u J ≤ 3000000 * a ^ 10 at hp
  change budget n B d u J ≤ 4000000 * a ^ 10
  unfold budget
  omega

/-- The same executed accumulator returns a valid bounded dictionary and an
exact frame for every other stack. Its polynomial local time controls every
prefix, including all caller storage and all native arithmetic temporaries. -/
theorem accumulate_run_space (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p ^ t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (seed factor : List (Product.Entry n (baseWidth p t) d))
    (hs : TruncatedRingProgram.Good ∅ u J seed) (hf : TruncatedRingProgram.Good ∅ u J factor) (a : Factor.Data)
    (hlow : Factor.lowReady a (Product.idle M.bits width cache.zero.val
      (RingTriple.tableEncoding table) degree (List.replicate u true) (List.replicate J true)))
    (hseed : a.stacks 151 = Product.bytes seed)
    (hfactor : a.stacks 67 = Product.bytes factor)
    (h61 : a.stacks 61 = []) (h70 : a.stacks 70 = []) (h159 : a.stacks 159 = []) :
    let result := Product.run p t M cache table u J seed factor []
    let program := compiled Factor.accumulate 67 151
    ∃ steps b, steps ≤ budget n (baseWidth p t) d u J ∧ TruncatedRingProgram.Good ∅ u J result ∧
      Eval Factor.accumulate steps a b ∧
      b.stacks = Function.update (Function.update a.stacks 67 []) 151 (Product.bytes result) ∧
      (Product.bytes result).length ≤ byteBound n (baseWidth p t) d u J ∧
      Trace program (steps + 1) (a.withPC (some program.entry)) (b.withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
        Trace program prefixSteps (a.withPC (some program.entry)) intermediate →
        dataBits intermediate ≤ stackBits a.stacks + budget n (baseWidth p t) d u J + 1 := by
  dsimp only
  obtain ⟨steps, b, hsteps, he, hb⟩ := Factor.accumulate_eval p t M cache hz table
    degree width hd hw u J seed factor a hlow hseed hfactor h61 h70 h159
  have hgood := TruncatedRingProgram.product_good p t M cache table ∅ u J seed factor hs hf
  have hslen := TruncatedRingProgram.empty_bytes_length_le hs
  have hflen := TruncatedRingProgram.empty_bytes_length_le hf
  have hrlen := TruncatedRingProgram.empty_bytes_length_le hgood
  have hwork := TruncatedRingProgram.product_work_le p t M cache table u J seed factor hs hf
  have hbound : steps ≤ budget n (baseWidth p t) d u J := by
    dsimp only [budget, byteBound]
    omega
  refine ⟨steps, b, hbound, hgood, he, hb, hrlen, compiled_halt_trace he 67 151, ?_⟩
  intro prefixSteps intermediate hp htrace
  have hgrowth := trace_dataBits (compiled Factor.accumulate 67 151) htrace
  change dataBits intermediate ≤ stackBits a.stacks + prefixSteps at hgrowth
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace
