import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpGlobalRowInputs
import OAI.Algorithms.SubexponentialSAT.SubexpGlobalRowValues
import OAI.Algorithms.SubexponentialSAT.SubexpGlobalRowPacking
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowAssemblyCost
import OAI.Algorithms.SubexponentialSAT.BitProgramSelectedSpace

namespace OAI.Algorithms

/-! The same-block branch invokes the actual matrix-to-row source program.
Its cost depends only on the selected input masters and live row indices.
Metadata cleanup is bounded by actual stack growth, excluding arbitrary
parser tails and previously accumulated output rows. -/

namespace SubexponentialSAT.SubexpGlobalRowUniversal

open BitProgram StructuredCalls SubexpDenseRowTableProgram
  SubexpGlobalRowLookup SubexpGlobalRowSelection SubexpGlobalRowInputs
open Subexp.ConstructivePacking

abbrev Source := Subexp.UniversalRowAssembly.Data

def inner (a : Data) : Source := projectState (Fin.castAdd 9) id a

def staged {r Q Δ : ℕ} (a : Data) (i : Fin Δ)
    (u y : MulticolorTypes.UniversalType r Q Δ) : Data :=
  ⟨a.regs, Function.update (Function.update (Function.update a.stacks
    272 (Subexp.CollisionProgram.encodeType u)) 275 (Subexp.CollisionProgram.encodeType y))
      284 (unary (i.val + 1))⟩

/-- One fixed row command; all dimensions and arithmetic data are inputs. -/
def command : Code := row Subexp.UniversalRowAssembly.callerCommand SubexpRowToTaylorCalls.command

theorem cleanup_cost_after_eval (c : Code) {n : ℕ} {a b : Data}
    (ha : HighClean a) (he : Eval c n a b) :
    WorkspaceCleanupProgram.cost cleanupPorts b ≤ 2 * n + 51 := by
  have hg := BitProgram.trace_listStackBits (compiled c 0 0) cleanupPorts cleanupPorts_nodup
    (compiled_trace he 0 0)
  change (cleanupPorts.map (fun i => (b.stacks i).length)).sum ≤
    (cleanupPorts.map (fun i => (a.stacks i).length)).sum + n at hg
  have hm : cleanupPorts.map (fun i => (a.stacks i).length) = cleanupPorts.map (fun _ => 0) := by
    apply List.map_congr_left
    intro i hi
    rw [ha i (cleanup_mem_high i hi)]
    rfl
  have hz : (cleanupPorts.map (fun i => (a.stacks i).length)).sum = 0 := by rw [hm]; simp
  rw [hz, Nat.zero_add] at hg
  change 2 * (cleanupPorts.map (fun i => (b.stacks i).length)).sum + 3 * 17 ≤ _
  omega

theorem staged_boundInputs {r Q Δ : ℕ} (a b : Data) (i : Fin Δ)
    (u y : MulticolorTypes.UniversalType r Q Δ)
    (hframe : ∀ j : Fin 288, j ∉ cleanupPorts → b.stacks j = a.stacks j)
    (hu : b.stacks 272 = Subexp.CollisionProgram.encodeType u)
    (hy : b.stacks 275 = Subexp.CollisionProgram.encodeType y)
    (hi : b.stacks 284 = unary (i.val + 1)) :
    Subexp.UniversalRowAssembly.SameBoundInputs (inner b) (inner (staged a i u y)) := by
  intro j hj
  change b.stacks j = (staged a i u y).stacks j
  by_cases h272 : j = 272
  · subst j; simpa [staged] using hu
  by_cases h275 : j = 275
  · subst j; simpa [staged] using hy
  by_cases h284 : j = 284
  · subst j; simpa [staged] using hi
  have hn : j ∉ cleanupPorts := by
    simp only [Subexp.UniversalRowAssembly.boundInputPorts, List.mem_cons,
      List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact (h272 rfl).elim
      | exact (h275 rfl).elim
      | exact (h284 rfl).elim
      | decide
  simpa [staged, h272, h275, h284] using hframe j hn

variable {p r Q Δ D : ℕ} [Fact p.Prime]
variable (source : SubexpSelectedConversions.Prepared p 0)
variable (xs : List (ZMod p)) (inverse negative : Fin Q → Word)
  (difference : Fin Q → Fin Q → Word)

noncomputable def sourceCost (a : Data) (i : Fin Δ)
    (u y : MulticolorTypes.UniversalType r Q Δ) : ℕ :=
  Subexp.UniversalRowAssembly.executionBound p i u y xs
    (Subexp.UniversalRowAssembly.computedTables p i u y xs inverse negative difference)
    (inner (staged a i u y)) + 1

theorem sourceCost_sameContext (a b : Data) (i : Fin Δ)
    (u y : MulticolorTypes.UniversalType r Q Δ)
    (h : SubexpDenseRowTableAssembly.SameContext a.stacks b.stacks) :
    sourceCost xs inverse negative difference b i u y =
      sourceCost xs inverse negative difference a i u y := by
  have hs : Subexp.UniversalRowAssembly.SameBoundInputs
      (inner (staged b i u y)) (inner (staged a i u y)) := by
    intro j hj
    change (staged b i u y).stacks j = (staged a i u y).stacks j
    by_cases h272 : j = 272
    · subst j; simp [staged]
    by_cases h275 : j = 275
    · subst j; simp [staged]
    by_cases h284 : j = 284
    · subst j; simp [staged]
    have hn : j ∉ SubexpDenseRowTableAssembly.varyingPorts := by
      simp only [Subexp.UniversalRowAssembly.boundInputPorts, List.mem_cons,
        List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact (h272 rfl).elim
        | exact (h275 rfl).elim
        | exact (h284 rfl).elim
        | decide
    simpa [staged, h272, h275, h284] using h j hn
  exact congrArg (fun n : ℕ => n + 1)
    (Subexp.UniversalRowAssembly.executionBound_congr p i u y xs
      (Subexp.UniversalRowAssembly.computedTables p i u y xs inverse negative difference)
      (inner (staged b i u y)) (inner (staged a i u y)) hs)

def classifyCost (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (scopes : List (List ℕ)) (e : ℕ) (v w : Fin D) (block : Fin P.blockCount) : ℕ :=
  400 * (SubexpGlobalRowPacking.volume P Subexp.CollisionProgram.encodeType v)^2 +
  400 * (SubexpGlobalRowPacking.volume P Subexp.CollisionProgram.encodeType w)^2 +
  27 * block.val + SubexpIncidenceSlotProgram.budget scopes e v.val + 30

/-- Same-block source preparation, including real matrix computation and
clearing every metadata stack. The only final change is source code26. -/
theorem prepare_eval
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (scopes : List (List ℕ)) (e : ℕ) (he : e ≤ scopes.length)
    (v w : Fin D) (block : Fin P.blockCount) (i : Fin Δ)
    (u y : MulticolorTypes.UniversalType r Q Δ)
    (hv : P.lookup v = some (block,u)) (hw : P.lookup w = some (block,y))
    (hslot : SubexpIncidenceSlotProgram.degree scopes e v.val = i.val)
    (h2 : (2 : ZMod p) ≠ 0) (a : Data)
    (hm : Masters p r Q xs inverse negative difference a)
    (htable : a.stacks 265 = SubexpGlobalRowPacking.table P Subexp.CollisionProgram.encodeType)
    (hscopes : a.stacks 256 = SubexpIncidenceSlotProgram.scopeBits scopes)
    (hfactor : a.stacks 261 = unary e)
    (hsource : a.stacks 260 = SubexpGlobalRowPacking.key v)
    (htarget : a.stacks 262 = SubexpGlobalRowPacking.key w)
    (ha : HighClean a)
    (hzero : a.stacks 131 = SubexpFlatAdd.encode source.zero)
    (hone : a.stacks 132 = SubexpFlatAdd.encode source.one) :
    ∃ n ≤ 3 * (classifyCost P scopes e v w block +
      sourceCost xs inverse negative difference a i u y) + 52, ∃ regs,
      Eval (prepare Subexp.UniversalRowAssembly.callerCommand) n a
        ⟨regs, Function.update a.stacks 26
          (SubexpRowToTaylorCalls.code
            (SubexpGlobalRowValues.expression source i u y xs inverse negative difference))⟩ := by
  obtain ⟨nc, hnc, b, hc, h5, h6, hb⟩ := SubexpGlobalRowPacking.classify_sameBlock
    P Subexp.CollisionProgram.encodeType v w block u y hv hw scopes e he a
    htable hscopes hfactor hsource htarget ha
  have hframe (j : Fin 288) (hj : j ∉ cleanupPorts) : b.stacks j = a.stacks j := by
    have hn : j ≠ 284 := by intro heq; subst j; exact hj (by decide)
    rw [hb, Function.update_of_ne hn, secondStore_frame _ _ j hj, firstStore_frame _ _ j hj]
  have hu : b.stacks 272 = Subexp.CollisionProgram.encodeType u := by
    rw [hb]; simp [firstStore, secondStore, Subexp.GlobalBasisMetadata.Metadata.typeCode]
  have hy : b.stacks 275 = Subexp.CollisionProgram.encodeType y := by
    rw [hb]; simp [secondStore, Subexp.GlobalBasisMetadata.Metadata.typeCode]
  have hi : b.stacks 284 = unary (i.val + 1) := by rw [hb]; simp [hslot]
  have hinput := Masters.prepared p r Q xs inverse negative difference i u y hm hframe hu hy hi
  obtain ⟨nu, hnu, c, huRun, hstore, hregs⟩ :=
    Subexp.UniversalRowAssembly.caller_eval_prepared p i u y xs h2 inverse negative difference b hinput
  have hnu' : nu ≤ sourceCost xs inverse negative difference a i u y := by
    rw [Subexp.UniversalRowAssembly.executionBound_congr p i u y xs
      (Subexp.UniversalRowAssembly.computedTables p i u y xs inverse negative difference)
      (projectState (Fin.castAdd 9) id b) (inner (staged a i u y))
      (staged_boundInputs a b i u y hframe hu hy hi)] at hnu
    exact hnu
  have hword := SubexpGlobalRowValues.sourceWord_eq_code source i u y xs inverse negative difference
    hm.inverseWidth hm.negativeWidth hm.differenceWidth (projectState (Fin.castAdd 9) id b)
    ((hframe 131 (by decide)).trans hzero) ((hframe 132 (by decide)).trans hone)
  rw [hword] at hstore
  obtain ⟨regs, hp⟩ := prepare_universal_after_run Subexp.UniversalRowAssembly.callerCommand a b c
    (SubexpRowToTaylorCalls.code
      (SubexpGlobalRowValues.expression source i u y xs inverse negative difference)) ha hc h5 huRun hstore hframe
  have hcleanup := cleanup_cost_after_eval (.seq classify Subexp.UniversalRowAssembly.callerCommand)
    ha (hc.seq huRun)
  refine ⟨_, ?_, regs, hp⟩
  change nc ≤ classifyCost P scopes e v w block at hnc
  omega

end SubexponentialSAT.SubexpGlobalRowUniversal

end OAI.Algorithms
