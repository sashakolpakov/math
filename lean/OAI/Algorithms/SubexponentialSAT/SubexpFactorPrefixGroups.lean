import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPrefixPairs

namespace OAI.Algorithms

/-! Actual scope-counted prefix grouping and frame construction. -/

namespace SubexponentialSAT.SubexpFactorPrefixProgram

open BitProgram StructuredCalls
open Subexp.FactorPacketCoordinates (Word Prefix originBytes taylorBytes prefixBytes)
open Subexp.FactorPacketRows (prefixStream)

attribute [local simp] Fin.coe_ofNat_eq_mod

def between (v : View) (os ts scopes acc : Word) : View :=
  {v with origins := os, todoTaylor := ts, todoScopes := scopes, scope := [], arity := [], count := [], origin := [], column := [], prefixData := [], reversePrefixes := [], prefixes := [], group := [], reverseGroups := acc, parseTmp := [], copyTmp := [], reverseTmp := []}

def groupBudget (scope : List ℕ) (ps : List Prefix) : ℕ :=
  9 * (scopeBytes scope).length +
  SubexpSunflowerProgram.CountRecords.loopSteps (scope.map Encoding.encodeNat) +
  15 * ps.length + pairsBudget ps + 10 * (prefixStream ps.reverse).length +
  8 * (prefixStream ps).length + 8 * (groupBytes ps).length + 42

theorem groupStep_eval (scope : List ℕ) (ps : List Prefix) (hlen : scope.length = ps.length)
    (regs : Fin 8 → Bool) (v : View) (ot tt rest acc : Word) :
    ∃ n ≤ groupBudget scope ps, ∃ rf, Eval groupStep n
      (state regs (between v (chunk originBytes ps ++ ot) (chunk taylorBytes ps ++ tt)
        (Encoding.frame (scopeBytes scope) ++ rest) acc))
      (state rf (between v ot tt rest (true :: (Encoding.frame (groupBytes ps) ++ acc)))) := by
  let v0 := between v (chunk originBytes ps ++ ot) (chunk taylorBytes ps ++ tt)
    (Encoding.frame (scopeBytes scope) ++ rest) acc
  let v1 := {v0 with todoScopes := rest, scope := scopeBytes scope}
  obtain ⟨d1,h1,hs1⟩ := readWord_eval 5 6 (by decide) (by decide) (by decide)
    (state regs v0) (scopeBytes scope) rest rfl rfl rfl
  have hd1 : d1 = state d1.regs v1 := by
    apply SubexpScanPrimitives.state_ext <;> try rfl
    simpa only [state, update_todoScopes, update_scope] using hs1
  rw [hd1] at h1
  let v2 := {v1 with scope := [], arity := List.replicate ps.length true}
  obtain ⟨d2,h2,hs2⟩ := countScope_eval (scope.map Encoding.encodeNat) (state d1.regs v1)
    (by rw [encodeList_map]; rfl) rfl
  have hd2 : d2 = state d2.regs v2 := by
    apply SubexpScanPrimitives.state_ext <;> try rfl
    simpa [state, v2, hlen] using hs2
  rw [hd2] at h2
  let v3 := {v2 with count := List.replicate ps.length true}
  obtain ⟨d3,h3,hs3⟩ := copy_eval 7 8 (by decide) (by decide) (by decide) (state d2.regs v2) rfl
  have hd3 : d3 = state d3.regs v3 := by
    apply SubexpScanPrimitives.state_ext <;> try rfl
    simpa [state, StackRoutines.copyStacks, v3, v2, v1, v0, between] using hs3
  rw [hd3] at h3
  let r4 := Function.update d3.regs (0 : Fin 8) false
  let v4 := {v3 with reversePrefixes := [false]}
  have h4 : Eval (push 12 false) 2 (state d3.regs v3) (state r4 v4) := by
    simpa [state, v4, v3, v2, v1, v0, between] using push_eval 12 false (state d3.regs v3)
  obtain ⟨r5,h5⟩ := pairs_eval ps r4 v4 ot tt [false]
  let v5 := {v4 with origins := ot, todoTaylor := tt, count := [], reversePrefixes := prefixStream ps.reverse}
  have h5' : Eval pairs (pairsBudget ps) (state r4 v4) (state r5 v5) := by
    simpa [working, chunk_encodeList, prefixStream, v5, v4, v3, v2, v1, v0, between] using h5
  let r6 := Function.update r5 (0 : Fin 8) false
  let v6 := {v5 with prefixes := [false]}
  have h6 : Eval (push 13 false) 2 (state r5 v5) (state r6 v6) := by
    simpa [state, v6, v5, v4, v3, v2, v1, v0, between] using push_eval 13 false (state r5 v5)
  obtain ⟨nr,hnr,d7,h7,hs7⟩ := reverseAt_eval prefixReversePorts (state r6 v6)
    (ps.reverse.map prefixBytes) []
    (by
      change prefixStream ps.reverse = Encoding.encodeList id (ps.reverse.map prefixBytes)
      rw [encodeList_map]
      rfl) rfl rfl
  let v7 := {v6 with reversePrefixes := [], prefixes := prefixStream ps}
  have hd7 : d7 = state d7.regs v7 := by
    apply SubexpScanPrimitives.state_ext <;> try rfl
    simpa [state, prefixReversePorts, encodeList_map, prefixStream, v7] using hs7
  rw [hd7] at h7
  have hnr' : nr ≤ 10 * (prefixStream ps.reverse).length := by
    simpa only [prefixStream,encodeList_map,Function.id_comp] using hnr
  let v8 := {v7 with prefixes := [], group := Encoding.frame (prefixStream ps)}
  obtain ⟨d8,h8,hs8⟩ := emitFrame_eval 13 14 (by decide) (by decide) (by decide) (state d7.regs v7) rfl
  have hd8 : d8 = state d8.regs v8 := by
    apply SubexpScanPrimitives.state_ext <;> try rfl
    simpa [state, v8, v7, v6, v5, v4, v3, v2, v1, v0, between] using hs8
  rw [hd8] at h8
  let v9 := {v8 with arity := [], group := groupBytes ps}
  obtain ⟨d9,h9,hs9⟩ := emitFrame_eval 7 14 (by decide) (by decide) (by decide) (state d8.regs v8) rfl
  have hd9 : d9 = state d9.regs v9 := by
    apply SubexpScanPrimitives.state_ext <;> try rfl
    simpa [state, v9, v8, v7, v6, v5, v4, v3, v2, v1, v0, between, groupBytes] using hs9
  rw [hd9] at h9
  obtain ⟨d10,h10,hs10⟩ := emitRecord_eval 14 15 (by decide) (by decide) (by decide)
    (state d9.regs v9) rfl
  have hd10 : d10 = state d10.regs (between v ot tt rest (true :: (Encoding.frame (groupBytes ps) ++ acc))) := by
    apply SubexpScanPrimitives.state_ext <;> try rfl
    simpa [state, v9, v8, v7, v6, v5, v4, v3, v2, v1, v0, between] using hs10
  rw [hd10] at h10
  have hrun := h1.seq (h2.seq (h3.seq (h4.seq (h5'.seq (h6.seq (h7.seq (h8.seq (h9.seq h10))))))))
  refine ⟨_, ?_, d10.regs, hrun⟩
  simp only [state, store_arity, store_prefixes, store_group]
  dsimp [groupBudget, v9, v8, v7, v6, v5, v4, v3, v2, v1, v0, between]
  simp only [List.length_replicate]
  omega

end SubexponentialSAT.SubexpFactorPrefixProgram

end OAI.Algorithms
