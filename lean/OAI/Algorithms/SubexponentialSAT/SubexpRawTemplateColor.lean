import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateContext

namespace OAI.Algorithms

/-! One actual color iteration: select, expand its banks, append, and increment. -/

namespace SubexponentialSAT.SubexpRawTemplate

open BitProgram StructuredCalls SubexpScanPrimitives
open Subexp.ConstructivePacking

attribute [local simp] Fin.coe_ofNat_eq_mod

variable {D r Q Δ : ℕ}

theorem groupBody_eval
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (items : List (SubexpFactorRoutingTraversal.Item r Q))
    (suffix : Word) (g : Fin r) (increments : List Word) (tail : Word) (d : Data)
    (hm : Masters P t items suffix d.stacks) (hw : ColorWork d.stacks)
    (hsource : d.stacks 204 = Encoding.frame (Encoding.encodeList id increments) ++ tail)
    (hcolor : d.stacks 219 = colorWord g.val) :
    ∃ n e, n ≤ groupStepCost P t items suffix g increments ∧ Eval groupBody n d e ∧
      e.stacks = Function.update (colorStore P t items g increments d.stacks) 204 tail := by
  let banks := Encoding.encodeList id increments
  let support := selectedSupport P t g.val
  let factors := routedBytes t g items
  let outside := selectedOutside P
  let group := colorGroupBytes P t items g increments
  let a := captured 204 206 banks tail d
  have hcap : Eval (capture 204 206 (by decide)) (9 * banks.length + 7) d a :=
    capture_eval 204 206 (by decide) (by decide) (by decide) banks tail d
      hsource hw.bank hw.scratch
  have hma : Masters P t items suffix a.stacks := by
    apply hm.of_frame
    intro i hi
    simp only [masterPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [a, captured]
  have hwa : WorkspaceEmpty a := by
    intro i hlo hhi
    have h204 : i ≠ 204 := by intro h; subst i; norm_num at hhi
    have h206 : i ≠ 206 := by intro h; subst i; norm_num at hhi
    simpa [a, captured, h204, h206] using hw.workspace i hlo hhi
  have ha219 : a.stacks 219 = colorWord g.val := by simp [a, captured, hcolor]
  obtain ⟨nf, b, hnf, hf, _hbr, hb⟩ := selectFactors_eval t g items suffix a hwa
    (by simpa [a, captured] using hw.factors) hma.assignment hma.packets
    (by simp [ha219]) hma.node hma.colors hma.width
  rw [factorCost_eq P t g items suffix (colorWord g.val) a hma ha219] at hnf
  have hmb : Masters P t items suffix b.stacks := by
    apply hma.of_frame
    intro i hi
    simp only [masterPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [hb]
  have hwb : WorkspaceEmpty b := by
    intro i hlo hhi
    have h210 : i ≠ 210 := by intro h; subst i; norm_num at hhi
    simpa [hb, h210] using hwa i hlo hhi
  have hb219 : b.stacks 219 = colorWord g.val := by simp [hb, ha219]
  obtain ⟨ns, c, hns, hs, _hcr, hc⟩ := selectSupport_eval P t b hwb
    (by simpa [hb, a, captured] using hw.support)
    (by simpa [hb, a, captured] using hw.outside)
    hmb.dimension hmb.node hmb.colors hmb.metadata
  rw [hb219] at hns
  rw [hb219, colorWord_value] at hc
  let u := cleared 223 c
  have hc223 : c.stacks 223 = outside := by simp [hc, outside]
  have ho : Eval (clear 223) (2 * outside.length + 3) c u := by
    have he : Eval (clear 223) (2 * (c.stacks 223).length + 3) c u := clear_eval 223 c
    simpa only [hc223] using he
  have hu206 : u.stacks 206 = Encoding.encodeList id increments := by
    simp [u, cleared, hc, hb, a, captured, banks]
  have huw : GroupWork support factors u.stacks := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [u, cleared, hc, hb, a, captured] using hw.payload
    · simpa [u, cleared, hc, hb, a, captured] using hw.term
    · simpa [u, cleared, hc, hb, a, captured] using hw.scratch
    · simpa [u, cleared, hc, hb, a, captured] using hw.forward
    · simp [u, cleared, hc, support]
    · simp [u, cleared, hc, hb, factors]
  obtain ⟨ng, f, hng, hg, hh⟩ := group_eval support factors increments u hu206 huw
    (by simpa [u, cleared, hc, hb, a, captured] using hw.terms)
    (by simpa [u, cleared, hc, hb, a, captured] using hw.group)
  have hf216 : f.stacks 216 = group := by
    simp [hh, group, colorGroupBytes, support, factors]
  have hf218 : f.stacks 218 = [] := by
    simpa [hh, u, cleared, hc, hb, a, captured] using hw.scratch
  let m := recorded 216 211 f
  have ha : Eval (appendRecord 216 211) (8 * group.length + 9) f m := by
    have he : Eval (appendRecord 216 211) (8 * (f.stacks 216).length + 9) f m :=
      appendRecord_eval 216 211 (by decide) (by decide) (by decide) f hf218
    simpa only [hf216] using he
  let p := cleared 216 m
  have hm216 : m.stacks 216 = group := by simp [m, recorded, hf216]
  have hgclear : Eval (clear 216) (2 * group.length + 3) m p := by
    have he : Eval (clear 216) (2 * (m.stacks 216).length + 3) m p := clear_eval 216 m
    simpa only [hm216] using he
  let q := cleared 209 p
  have hp209 : p.stacks 209 = support := by
    simp [p, cleared, m, recorded, hh, u, cleared, hc, support]
  have hsclear : Eval (clear 209) (2 * support.length + 3) p q := by
    have he : Eval (clear 209) (2 * (p.stacks 209).length + 3) p q := clear_eval 209 p
    simpa only [hp209] using he
  let v := cleared 210 q
  have hq210 : q.stacks 210 = factors := by
    simp [q, cleared, p, m, recorded, hh, u, hc, hb, factors]
  have hfclear : Eval (clear 210) (2 * factors.length + 3) q v := by
    have he : Eval (clear 210) (2 * (q.stacks 210).length + 3) q v := clear_eval 210 q
    simpa only [hq210] using he
  have hv218 : v.stacks 218 = [] := by
    simpa [v, cleared, q, p, m, recorded] using hf218
  have hv219 : v.stacks 219 = colorWord g.val := by
    simp [v, cleared, q, p, m, recorded, hh, u, hc, hb219]
  let e := incremented v
  have hinc : Eval incrementColor (CounterPrograms.rippleCost true (colorWord g.val) + 1) v e := by
    have he : Eval incrementColor (CounterPrograms.rippleCost true (v.stacks 219) + 1) v e :=
      incrementColor_eval v hv218
    simpa only [hv219] using he
  have he := hcap.seq (hf.seq (hs.seq (ho.seq (hg.seq
    (ha.seq (hgclear.seq (hsclear.seq (hfclear.seq hinc))))))))
  refine ⟨_, e, ?_, he, ?_⟩
  · dsimp [groupStepCost, colorGroupBytes] at ⊢
    dsimp [support, factors] at hng
    dsimp [banks, support, factors, outside, group, colorGroupBytes]
    omega
  · funext i
    by_cases hi204 : i = 204
    · subst i
      simp [e, incremented, v, cleared, q, p, m, recorded, hh, u, hc, hb, a, captured]
    by_cases hi206 : i = 206
    · subst i
      simp [e, incremented, v, cleared, q, p, m, recorded, hh, colorStore, hw.bank]
    by_cases hi209 : i = 209
    · subst i
      simp [e, incremented, v, cleared, q, colorStore, hw.support]
    by_cases hi210 : i = 210
    · subst i
      simp [e, incremented, v, cleared, colorStore, hw.factors]
    by_cases hi211 : i = 211
    · subst i
      simp [e, incremented, v, cleared, q, p, m, recorded, hf216, hh, u, hc, hb,
        a, captured, colorStore, group]
    by_cases hi216 : i = 216
    · subst i
      simp [e, incremented, v, cleared, q, p, colorStore, hw.group]
    by_cases hi219 : i = 219
    · subst i
      simp [e, incremented, hv219, colorStore, colorWord]
    by_cases hi223 : i = 223
    · subst i
      simp [e, incremented, v, cleared, q, p, m, recorded, hh, u, colorStore, hw.outside]
    · simp [e, incremented, v, cleared, q, p, m, recorded, hh, u, hc, hb, a, captured,
        colorStore, hi204, hi206, hi209, hi210, hi211, hi216, hi219, hi223]

end SubexponentialSAT.SubexpRawTemplate

end OAI.Algorithms
