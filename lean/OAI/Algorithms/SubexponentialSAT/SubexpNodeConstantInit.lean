import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeRawConstants

namespace OAI.Algorithms

/-! Complete finite initialization of both raw literals and scalar one. -/

namespace SubexponentialSAT.SubexpNodeConstantInit

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpNodeRawConstants SubexpArgumentEmitLoop

abbrev Data := State 16 256

theorem prepared_input (d : Data) (one : Bool) (D : ℕ) (hw : WorkEmpty d)
    (hD : d.stacks 109 = List.replicate D true)
    (hI : d.stacks 92 = List.replicate (SubexpSymbolicCost.indexBits D) true) :
    projectState registers ports (prepared one d) =
      scalarInput (prepared one d) D (d.stacks (source one)) := by
  apply state_ext
  · funext i
    fin_cases i <;> rfl
  · funext i
    have hs := prepared_stacks d one hw
    fin_cases i <;>
      simp [projectState, scalarInput, ready, ports,
        Fin.coe_ofNat_eq_mod, unary, hs, hD, hI] <;>
      exact hw _ (by decide) (by decide)

abbrev raw (one : Bool) : Cmd 16 256 :=
  .seq (prepare one) (.seq call (.seq (transfer 203 215)
    (.seq (transfer 215 (destination one)) (SubexpNodeCacheSetup.clears [207, 208]))))

def rawCost (D : ℕ) (coefficient : List Bool) : ℕ :=
  constantCost D (SubexpSymbolicCost.indexBits D) false coefficient +
    14 * coefficient.length + 9 * (D + SubexpSymbolicCost.indexBits D) +
      6 * (SubexpScalarLiteralProgram.rawLiteral D coefficient).length + 38

theorem raw_eval (d : Data) (one : Bool) (D : ℕ)
    (h0 : d.stacks 0 = []) (hw : WorkEmpty d)
    (hD : d.stacks 109 = List.replicate D true)
    (hI : d.stacks 92 = List.replicate (SubexpSymbolicCost.indexBits D) true)
    (hdst : d.stacks (destination one) = []) :
    ∃ out : Data, Eval (raw one) (rawCost D (d.stacks (source one))) d out ∧
      out.stacks = Function.update d.stacks (destination one)
        (SubexpScalarLiteralProgram.rawLiteral D (d.stacks (source one))) := by
  have hp := prepare_eval d one h0 hw
  have hps := prepared_stacks d one hw
  obtain ⟨e, he, hes⟩ := call_eval (prepared one d) D (d.stacks (source one))
    (prepared_input d one D hw hD hI)
  let f := afterTransfer e 203 215 0 1
  let g := afterTransfer f 215 (destination one) 0 1
  let out := SubexpNodeCacheSetup.cleared [207, 208] g
  have ht := transfer_eval e 203 215 0 1 (by decide) (by decide)
  have hu := transfer_eval f 215 (destination one) 0 1
    (by cases one <;> decide) (by decide)
  have hc := SubexpNodeCacheSetup.clears_eval [207, 208] g
  have he215 : e.stacks 215 = [] := by
    simpa [hes, hps] using hw 215 (by decide) (by decide)
  have he203 : e.stacks 203 = SubexpScalarLiteralProgram.rawLiteral D (d.stacks (source one)) := by
    simp [hes]
  have hf215 : f.stacks 215 = (SubexpScalarLiteralProgram.rawLiteral D (d.stacks (source one))).reverse := by
    simp [f, afterTransfer, StackRoutines.transferStacks, he215, he203]
  have hg207 : g.stacks 207 = List.replicate D true := by
    cases one <;> simp [g, f, afterTransfer, StackRoutines.transferStacks,
      destination, hes, hps, hD]
  have hg208 : g.stacks 208 = List.replicate (SubexpSymbolicCost.indexBits D) true := by
    cases one <;> simp [g, f, afterTransfer, StackRoutines.transferStacks,
      destination, hes, hps, hI]
  have hcost : SubexpNodeCacheSetup.clearCost [207, 208] g =
      2 * D + 2 * SubexpSymbolicCost.indexBits D + 6 := by
    simp [SubexpNodeCacheSetup.clearCost, SubexpNodeCacheSetup.clearOut, hg207, hg208]
    omega
  refine ⟨out, ?_, ?_⟩
  · have h := hp.seq (he.seq (ht.seq (hu.seq hc)))
    convert h using 1
    simp only [rawCost, hD, hI, List.length_replicate, he203, hf215, List.length_reverse, hcost]
    omega
  · funext i
    have hd200 := hw 200 (by decide) (by decide)
    have hd203 := hw 203 (by decide) (by decide)
    have hd207 := hw 207 (by decide) (by decide)
    have hd208 := hw 208 (by decide) (by decide)
    have hd215 := hw 215 (by decide) (by decide)
    by_cases hi200 : i = 200
    · subst i; cases one <;> simp [out, g, f, SubexpNodeCacheSetup.cleared,
        SubexpNodeCacheSetup.clearOut, afterTransfer, StackRoutines.transferStacks,
        hes, hps, destination, hd200]
    by_cases hi203 : i = 203
    · subst i; cases one <;> simp [out, g, f, SubexpNodeCacheSetup.cleared,
        SubexpNodeCacheSetup.clearOut, afterTransfer, StackRoutines.transferStacks,
        hes, hps, destination, hd203]
    by_cases hi207 : i = 207
    · subst i; cases one <;> simp [out, SubexpNodeCacheSetup.cleared,
        SubexpNodeCacheSetup.clearOut, destination, hd207]
    by_cases hi208 : i = 208
    · subst i; cases one <;> simp [out, SubexpNodeCacheSetup.cleared,
        SubexpNodeCacheSetup.clearOut, destination, hd208]
    by_cases hi215 : i = 215
    · subst i; cases one <;> simp [out, g, SubexpNodeCacheSetup.cleared,
        SubexpNodeCacheSetup.clearOut, afterTransfer, StackRoutines.transferStacks,
        destination, hd215]
    by_cases hidst : i = destination one
    · subst i; cases one <;>
        simp_all [out, g, f, SubexpNodeCacheSetup.cleared,
          SubexpNodeCacheSetup.clearOut, afterTransfer, StackRoutines.transferStacks,
          destination]
    · simp [out, g, f, SubexpNodeCacheSetup.cleared,
        SubexpNodeCacheSetup.clearOut, afterTransfer, StackRoutines.transferStacks,
        hes, hps, hi200, hi203, hi207, hi208, hi215, hidst]

abbrev zero : Cmd 16 256 := .base (.seq (.atom (.set 0 false)) (.atom (.push 122 0)))

def zeroState (d : Data) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks 122 (false :: d.stacks 122)⟩

theorem zero_eval (d : Data) : Eval zero 2 d (zeroState d) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 16) false) d).seq
    (StructuredProgram.Eval.atom (.push (122 : Fin 256) 0) _)
  exact .base (by simpa [zeroState, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using h)

/-- The exact expression compiler uses the empty raw coefficient list for
zero. Its encoding is one false bit, written by two ordinary instructions. -/
abbrev command : Cmd 16 256 := .seq zero (.seq (raw true) SubexpNodeConstants.unitInit)

abbrev program : Program 16 256 (size command + 1) := compiled command 120 124

def cost (d : Data) (D : ℕ) : ℕ :=
  2 + (rawCost D (d.stacks 120) + (14 * (d.stacks 10).length + 14))

theorem command_eval (d : Data) (D : ℕ)
    (h0 : d.stacks 0 = []) (hw : WorkEmpty d)
    (hD : d.stacks 109 = List.replicate D true)
    (hI : d.stacks 92 = List.replicate (SubexpSymbolicCost.indexBits D) true)
    (h122 : d.stacks 122 = []) (h123 : d.stacks 123 = []) (h124 : d.stacks 124 = [])
    (hwidth : 0 < (d.stacks 10).length) :
    ∃ out : Data, Eval command (cost d D) d out ∧
      out.stacks = Function.update (Function.update (Function.update d.stacks
        122 [false])
        123 (SubexpScalarLiteralProgram.rawLiteral D (d.stacks 120)))
        124 (SubexpLiftRing.fixedBits (d.stacks 10).length 1) := by
  let e := zeroState d
  have he := zero_eval d
  have hes : e.stacks = Function.update d.stacks 122 [false] := by
    simp [e, zeroState, h122]
  have hew : WorkEmpty e := by
    intro i hi hj
    have hn : i ≠ 122 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
    simpa [hes, destination, hn] using hw i hi hj
  obtain ⟨f, hf, hfs⟩ := raw_eval e true D
    (by simpa [hes, destination] using h0) hew
    (by simpa [hes, destination] using hD) (by simpa [hes, destination] using hI)
    (by simpa [hes, destination] using h123)
  have hsmall : ∀ i : Fin 256, i ≠ 122 → i ≠ 123 → f.stacks i = d.stacks i := by
    intro i h122' h123'
    simp [hfs, hes, destination, h122', h123']
  obtain ⟨out, hu, hus⟩ := SubexpNodeConstants.unit_init_eval f
    ((hsmall 0 (by decide) (by decide)).trans h0)
    ((hsmall 124 (by decide) (by decide)).trans h124)
    ((hsmall 215 (by decide) (by decide)).trans (hw 215 (by decide) (by decide)))
    ((hsmall 216 (by decide) (by decide)).trans (hw 216 (by decide) (by decide)))
    (by simpa only [hsmall 10 (by decide) (by decide)] using hwidth)
  refine ⟨out, ?_, ?_⟩
  · have h := he.seq (hf.seq hu)
    convert h using 1
    all_goals simp [cost, source, hes, hsmall]
  · simpa [hfs, hes, source, destination] using hus

theorem program_trace (d : Data) (D : ℕ)
    (h0 : d.stacks 0 = []) (hw : WorkEmpty d)
    (hD : d.stacks 109 = List.replicate D true)
    (hI : d.stacks 92 = List.replicate (SubexpSymbolicCost.indexBits D) true)
    (h122 : d.stacks 122 = []) (h123 : d.stacks 123 = []) (h124 : d.stacks 124 = [])
    (hwidth : 0 < (d.stacks 10).length) :
    ∃ out : Data, Trace program (cost d D + 1)
      (d.withPC (some program.entry)) (out.withPC none) ∧
      out.stacks = Function.update (Function.update (Function.update d.stacks
        122 [false])
        123 (SubexpScalarLiteralProgram.rawLiteral D (d.stacks 120)))
        124 (SubexpLiftRing.fixedBits (d.stacks 10).length 1) := by
  obtain ⟨out, he, hs⟩ := command_eval d D h0 hw hD hI h122 h123 h124 hwidth
  exact ⟨out, compiled_halt_trace he 120 124, hs⟩

end SubexponentialSAT.SubexpNodeConstantInit

end OAI.Algorithms
