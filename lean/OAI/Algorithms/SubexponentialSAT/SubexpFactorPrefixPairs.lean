import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPrefixServices
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPrefixSemantics

namespace OAI.Algorithms

/-! Actual aligned origin/Taylor traversal for one factor. -/

namespace SubexponentialSAT.SubexpFactorPrefixProgram

open BitProgram StructuredCalls
open Subexp.FactorPacketCoordinates (Word Prefix originBytes taylorBytes prefixBytes)

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem prefixBytes_eq (p : Prefix) :
    prefixBytes p = Encoding.frame (originBytes p) ++ Encoding.frame (taylorBytes p) := rfl

def working (v : View) (os ts acc : Word) : View :=
  {v with origins := os, todoTaylor := ts, origin := [], column := [], prefixData := [], reversePrefixes := acc, parseTmp := []}

def pairCost (p : Prefix) : ℕ :=
  17 * ((originBytes p).length + (taylorBytes p).length) +
    8 * (prefixBytes p).length + 42

theorem pairStep_eval (regs : Fin 8 → Bool) (v : View) (p : Prefix) (ot tt acc : Word) :
    ∃ rf, Eval pairStep (pairCost p)
      (state regs (working v (true :: (Encoding.frame (originBytes p) ++ ot))
        (true :: (Encoding.frame (taylorBytes p) ++ tt)) acc))
      (state rf (working v ot tt (true :: (Encoding.frame (prefixBytes p) ++ acc)))) := by
  let v0 := working v (true :: (Encoding.frame (originBytes p) ++ ot))
    (true :: (Encoding.frame (taylorBytes p) ++ tt)) acc
  let v1 := {v0 with origins := ot, origin := originBytes p}
  obtain ⟨d1, h1, hs1⟩ := readRecord_eval 0 9 (by decide) (by decide) (by decide)
    (state regs v0) (originBytes p) ot rfl rfl rfl
  have hd1 : d1 = state d1.regs v1 := by
    apply SubexpScanPrimitives.state_ext <;> try rfl
    simpa only [state, update_origins, update_origin] using hs1
  rw [hd1] at h1
  let v2 := {v1 with todoTaylor := tt, column := taylorBytes p}
  obtain ⟨d2, h2, hs2⟩ := readRecord_eval 4 10 (by decide) (by decide) (by decide)
    (state d1.regs v1) (taylorBytes p) tt rfl rfl rfl
  have hd2 : d2 = state d2.regs v2 := by
    apply SubexpScanPrimitives.state_ext <;> try rfl
    simpa only [state, update_todoTaylor, update_column] using hs2
  rw [hd2] at h2
  let v3 := {v2 with column := [], prefixData := Encoding.frame (taylorBytes p)}
  obtain ⟨d3, h3, hs3⟩ := emitFrame_eval 10 11 (by decide) (by decide) (by decide)
    (state d2.regs v2) rfl
  have hd3 : d3 = state d3.regs v3 := by
    apply SubexpScanPrimitives.state_ext <;> try rfl
    simpa [state, v2, v1, v0, working, v3] using hs3
  rw [hd3] at h3
  let v4 := {v3 with origin := [], prefixData := prefixBytes p}
  obtain ⟨d4, h4, hs4⟩ := emitFrame_eval 9 11 (by decide) (by decide) (by decide)
    (state d3.regs v3) rfl
  have hd4 : d4 = state d4.regs v4 := by
    apply SubexpScanPrimitives.state_ext <;> try rfl
    simpa [state, v4, v3, v2, v1, v0, working, prefixBytes_eq] using hs4
  rw [hd4] at h4
  obtain ⟨d5, h5, hs5⟩ := emitRecord_eval 11 12 (by decide) (by decide) (by decide)
    (state d4.regs v4) rfl
  have hd5 : d5 = state d5.regs
      (working v ot tt (true :: (Encoding.frame (prefixBytes p) ++ acc))) := by
    apply SubexpScanPrimitives.state_ext <;> try rfl
    simpa [state, v4, v3, v2, v1, v0, working] using hs5
  rw [hd5] at h5
  refine ⟨d5.regs, ?_⟩
  have hrun := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  convert hrun using 1
  all_goals first
    | rfl
    | (simp only [state, store_column, store_origin, store_prefixData]
       dsimp [pairCost, v4, v3, v2, v1, v0, working]
       omega)

def pairLoopBudget (ps : List Prefix) : ℕ := (ps.map (fun p => pairCost p + 2)).sum + 1
def pairsBudget (ps : List Prefix) : ℕ := pairLoopBudget ps + 1

def readyPairs (regs : Fin 8 → Bool) (v : View) (ps : List Prefix) (ot tt acc : Word) : Data :=
  state (readRegs regs 5 4 (List.replicate ps.length true).head?)
    {working v (chunk originBytes ps ++ ot) (chunk taylorBytes ps ++ tt) acc with
      count := (List.replicate ps.length true).tail}

theorem readyPairs_nil (regs : Fin 8 → Bool) (v : View) (ot tt acc : Word) :
    (readyPairs regs v [] ot tt acc).regs 5 = false := by
  simp [readyPairs, state, readRegs]

theorem readyPairs_cons (regs : Fin 8 → Bool) (v : View) (p : Prefix)
    (ps : List Prefix) (ot tt acc : Word) :
    (readyPairs regs v (p :: ps) ot tt acc).regs 5 = true := by
  simp [readyPairs, state, readRegs, List.replicate_succ]

theorem pairLoop_eval (ps : List Prefix) (regs : Fin 8 → Bool) (v : View) (ot tt acc : Word) :
    ∃ rf, Eval pairLoop (pairLoopBudget ps)
      (readyPairs regs v ps ot tt acc)
      (state rf {working v ot tt (chunk prefixBytes ps.reverse ++ acc) with count := []}) := by
  induction ps generalizing regs acc with
  | nil =>
    refine ⟨(readyPairs regs v [] ot tt acc).regs, ?_⟩
    simpa [pairLoop, pairLoopBudget, readyPairs, chunk, state, working] using
      (Eval.while_false (body := pairBody) (readyPairs_nil regs v ot tt acc))
  | cons p ps ih =>
    let r0 := (readyPairs regs v (p :: ps) ot tt acc).regs
    let w := {v with count := List.replicate ps.length true}
    obtain ⟨r1, h1⟩ := pairStep_eval r0 w p
      (chunk originBytes ps ++ ot) (chunk taylorBytes ps ++ tt) acc
    have h1' : Eval pairStep (pairCost p) (readyPairs regs v (p :: ps) ot tt acc)
        (state r1 (working w (chunk originBytes ps ++ ot) (chunk taylorBytes ps ++ tt)
          (true :: (Encoding.frame (prefixBytes p) ++ acc)))) := by
      simpa [readyPairs, r0, w, working, state, chunk, List.replicate_succ,
        List.append_assoc] using h1
    have h2 := pop_eval 8 5 4
      (state r1 (working w (chunk originBytes ps ++ ot) (chunk taylorBytes ps ++ tt)
        (true :: (Encoding.frame (prefixBytes p) ++ acc))))
    have h2' : Eval popCount 1
        (state r1 (working w (chunk originBytes ps ++ ot) (chunk taylorBytes ps ++ tt)
          (true :: (Encoding.frame (prefixBytes p) ++ acc))))
        (readyPairs r1 v ps ot tt (true :: (Encoding.frame (prefixBytes p) ++ acc))) := by
      simpa [popCount, state, readyPairs, working, w] using h2
    obtain ⟨rf, hr⟩ := ih r1 (true :: (Encoding.frame (prefixBytes p) ++ acc))
    have hacc : chunk prefixBytes ps.reverse ++ (true :: (Encoding.frame (prefixBytes p) ++ acc)) =
        chunk prefixBytes (p :: ps).reverse ++ acc := by
      simp [List.reverse_cons, chunk_append, chunk, List.append_assoc]
    rw [hacc] at hr
    refine ⟨rf, ?_⟩
    have hrun := Eval.while_true (readyPairs_cons regs v p ps ot tt acc) (h1'.seq h2') hr
    convert hrun using 1
    all_goals simp [pairLoopBudget]
    all_goals omega

theorem pairs_eval (ps : List Prefix) (regs : Fin 8 → Bool) (v : View) (ot tt acc : Word) :
    ∃ rf, Eval pairs (pairsBudget ps)
      (state regs {working v (chunk originBytes ps ++ ot) (chunk taylorBytes ps ++ tt) acc with
        count := List.replicate ps.length true})
      (state rf {working v ot tt (chunk prefixBytes ps.reverse ++ acc) with count := []}) := by
  have hp := pop_eval 8 5 4
    (state regs {working v (chunk originBytes ps ++ ot) (chunk taylorBytes ps ++ tt) acc with
      count := List.replicate ps.length true})
  have hp' : Eval popCount 1
      (state regs {working v (chunk originBytes ps ++ ot) (chunk taylorBytes ps ++ tt) acc with
        count := List.replicate ps.length true})
      (readyPairs regs v ps ot tt acc) := by
    simpa only [popCount, state, store_count, update_count, readyPairs] using hp
  obtain ⟨rf, hr⟩ := pairLoop_eval ps regs v ot tt acc
  refine ⟨rf, ?_⟩
  simpa only [pairs, pairsBudget, Nat.add_comm] using hp'.seq hr

end SubexponentialSAT.SubexpFactorPrefixProgram

end OAI.Algorithms
