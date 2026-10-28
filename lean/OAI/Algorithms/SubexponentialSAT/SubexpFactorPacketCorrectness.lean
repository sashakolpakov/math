import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPacketStage
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPacketRows
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPrefixGrouping

namespace OAI.Algorithms

/-! The original-order physical packet stream is the typed packet stream.

The hypotheses identify individual table rows and a common coefficient cache.
There is no assumed equality for the produced packet stream. The scope lengths
drive the actual grouping of the flattened origin and Taylor inputs.
-/

namespace SubexponentialSAT.SubexpFactorPacketCorrectness

open BitProgram
open SubexpSelectedConversions
open SubexpFactorPacketProvenance (Code)


/-- One occurrence in the original factor list. Repeated occurrences are kept.
Its scope fixes the number of incidence records consumed by the producer. -/
structure FactorInput (p D : ℕ) where
  scope : List ℕ
  degree : ℕ
  data : SubexpFactorPacketProvenance.Input p D p scope.length degree
  answers : List Bool

variable {p D : ℕ} [Fact p.Prime]
variable (source : Prepared p 0) (target : Prepared p D) (theta : Code p D)

def factorPrefixes (f : FactorInput p D) :
    List Subexp.FactorPacketCoordinates.Prefix :=
  SubexpFactorPacketProvenance.prefixes source target theta f.data

def typedFactors (fs : List (FactorInput p D)) : List (List Subexp.FactorBlueprint.Row) :=
  fs.map (fun f => (SubexpFactorPacketProvenance.blueprintRows source target theta f.data).map
    SubexpBlueprintRows.Row.packet)

variable (cache : List (List (Code p D))) (modulus : List Bool)
variable (zero one : Code p D)

/-- Initial finite data, in the order emitted by the scope, Taylor, origin,
and Boolean-table producers. The common cache is the full Lagrange cache. -/
def physicalInputs (fs : List (FactorInput p D)) : SubexpFactorPacketProgram.Inputs where
  origins := ((fs.map (factorPrefixes source target theta)).flatten).map
    Subexp.FactorPacketCoordinates.Prefix.origin
  columns := ((fs.map (factorPrefixes source target theta)).flatten).map
    Subexp.FactorPacketCoordinates.Prefix.taylor
  scopes := fs.map FactorInput.scope
  tables := fs.map FactorInput.answers
  cache := cache.map (List.map SubexpQuarticFlatNeg.flat)
  modulus := modulus
  zero := SubexpQuarticFlatNeg.flat zero
  one := SubexpQuarticFlatNeg.flat one

theorem physical_groups (fs : List (FactorInput p D)) :
    SubexpFactorPacketProgram.groups (physicalInputs source target theta cache modulus zero one fs) =
      fs.map (factorPrefixes source target theta) := by
  apply SubexpFactorPrefixProgram.grouped_of_pieces
  simp only [physicalInputs, List.map_map, Function.comp_def, factorPrefixes, SubexpFactorPacketProvenance.prefixes,
    List.length_ofFn]

theorem physical_factorInputs (fs : List (FactorInput p D)) :
    SubexpFactorPacketProgram.factorInputs (physicalInputs source target theta cache modulus zero one fs) =
      fs.map (fun f => SubexpFactorPacketLocal.Input.mk
        (factorPrefixes source target theta f) f.answers) := by
  unfold SubexpFactorPacketProgram.factorInputs
  rw [physical_groups]
  change (((fs.map (factorPrefixes source target theta)).zip
    (fs.map FactorInput.answers)).map _) = _
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      simpa only [List.map_cons, List.zip_cons_cons] using
        congrArg (SubexpFactorPacketLocal.Input.mk
          (factorPrefixes source target theta f) f.answers :: ·) ih

theorem physical_alignment (fs : List (FactorInput p D)) :
    let i := physicalInputs source target theta cache modulus zero one fs
    i.origins.length = i.columns.length ∧
    (i.scopes.map List.length).sum = i.origins.length ∧
    i.tables.length = i.scopes.length := by
  dsimp only [physicalInputs]
  simp only [List.length_map, List.length_flatten, List.map_map, Function.comp_def,
    factorPrefixes, SubexpFactorPacketProvenance.prefixes, List.length_ofFn, and_self]

theorem producedFactors_eq (fs : List (FactorInput p D))
    (hp : BinaryArithmetic.toNat modulus = p)
    (hc : ∀ f ∈ fs, f.data.cache = cache)
    (hlen : ∀ f ∈ fs, f.answers.length = p ^ f.scope.length)
    (hrows : ∀ f ∈ fs,
      f.data.rows = SubexpRankedTable.attachAnswers zero one f.answers) :
    SubexpFactorPacketProgram.producedFactors (physicalInputs source target theta cache modulus zero one fs) =
      typedFactors source target theta fs := by
  unfold SubexpFactorPacketProgram.producedFactors
  rw [physical_factorInputs, List.map_map]
  apply List.map_congr_left
  intro f hf
  have hprefix : (factorPrefixes source target theta f).length = f.scope.length := by
    simp only [factorPrefixes, SubexpFactorPacketProvenance.prefixes, List.length_ofFn]
  change (SubexpFactorRowStream.tableRows modulus
      (factorPrefixes source target theta f).length
      (SubexpQuarticFlatNeg.flat zero) (SubexpQuarticFlatNeg.flat one) f.answers).map
      (Subexp.FactorPacketRows.blueprintRow
        (cache.map (List.map SubexpQuarticFlatNeg.flat))
        (factorPrefixes source target theta f)) = _
  rw [hprefix]
  have h := SubexpFactorPacketProvenance.ranked_selected_rows_eq source target theta f.data modulus hp
    zero one f.answers (hlen f hf) (hrows f hf)
  simpa only [factorPrefixes, SubexpFactorPacketProvenance.encodedCache, hc f hf] using h

theorem output_eq_typedFactors (fs : List (FactorInput p D))
    (hp : BinaryArithmetic.toNat modulus = p)
    (hc : ∀ f ∈ fs, f.data.cache = cache)
    (hlen : ∀ f ∈ fs, f.answers.length = p ^ f.scope.length)
    (hrows : ∀ f ∈ fs,
      f.data.rows = SubexpRankedTable.attachAnswers zero one f.answers) :
    SubexpFactorPacketProgram.output (physicalInputs source target theta cache modulus zero one fs) =
      Encoding.encodeList Subexp.FactorBlueprint.encodeRows
        (typedFactors source target theta fs) := by
  rw [SubexpFactorPacketProgram.output_eq_encodeFactors,
    producedFactors_eq source target theta cache modulus zero one fs hp hc hlen hrows]

/-- The complete fixed packet program produces the exact typed factor stream
in original list order, and restores every stack except its consumed origin
input and packet output. All correctness premises describe initial local data. -/
theorem program_runs_typed (fs : List (FactorInput p D)) (d : SubexpFactorPacketProgram.Data)
    (ready : SubexpFactorPacketProgram.Ready d (physicalInputs source target theta cache modulus zero one fs))
    (hp : BinaryArithmetic.toNat modulus = p) (hcache : p ≤ cache.length)
    (hc : ∀ f ∈ fs, f.data.cache = cache)
    (hlen : ∀ f ∈ fs, f.answers.length = p ^ f.scope.length)
    (hrows : ∀ f ∈ fs,
      f.data.rows = SubexpRankedTable.attachAnswers zero one f.answers) :
    ∃ e : SubexpFactorPacketProgram.Data,
      RunsIn SubexpFactorPacketProgram.program
        (SubexpFactorPacketProgram.runtimeBound (physicalInputs source target theta cache modulus zero one fs))
        (d.withPC (some SubexpFactorPacketProgram.program.entry)) (e.withPC none) ∧
      e.stacks = Function.update (Function.update d.stacks 227 []) 225
        (Encoding.encodeList Subexp.FactorBlueprint.encodeRows
          (typedFactors source target theta fs)) := by
  obtain ⟨heq, hsize, ht⟩ := physical_alignment source target theta cache modulus zero one fs
  have hm : 0 < BinaryArithmetic.toNat
      (physicalInputs source target theta cache modulus zero one fs).modulus := by
    change 0 < BinaryArithmetic.toNat modulus
    rw [hp]
    exact (Fact.out : p.Prime).pos
  have hcache' : BinaryArithmetic.toNat
      (physicalInputs source target theta cache modulus zero one fs).modulus ≤
      (physicalInputs source target theta cache modulus zero one fs).cache.length := by
    simpa only [physicalInputs, List.length_map, hp] using hcache
  obtain ⟨e, he, hs⟩ := SubexpFactorPacketProgram.program_runsIn
    (physicalInputs source target theta cache modulus zero one fs) d ready heq hsize ht hm hcache'
  refine ⟨e, he, ?_⟩
  rw [output_eq_typedFactors source target theta cache modulus zero one fs hp hc hlen hrows] at hs
  exact hs

end SubexponentialSAT.SubexpFactorPacketCorrectness

end OAI.Algorithms
