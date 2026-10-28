import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDenseRowProducer
import OAI.Algorithms.SubexponentialSAT.SubexpDenseRowTableBound

namespace OAI.Algorithms

/-!
# Concrete dense-row producer bounds

This file separates the elementary dispatch/length estimates from the
universal-source estimate, then feeds the concrete costs into the measured
table traversal. No parser tail or previous row accumulator is a size input.
-/

namespace SubexponentialSAT.SubexpDenseRowServiceBound

open BitProgram StructuredCalls SubexpDenseRowTableProgram
open Subexp.ConstructivePacking SubexpLiftRing SubexpQuarticRing

theorem blockCount_le {D : ℕ} {U : Type*} [DecidableEq U]
    (P : PackingData (Fin D) U) : P.blockCount ≤ D := by
  have hmin : P.minCount P.types.values ≤ P.vertices.values.length := by
    cases P.types.values with
    | nil => exact le_rfl
    | cons u us => exact (min_le_left _ _).trans (P.bucket_length_le u)
  have hlen : P.vertices.values.length = D := by
    simpa only [Fintype.card_fin] using P.vertices.length_eq_card
  exact hmin.trans_eq hlen

theorem leftover_index_le {D : ℕ} {U : Type*} [DecidableEq U]
    (P : PackingData (Fin D) U) (v : Fin D) : P.leftovers.idxOf v ≤ D := by
  have hlen : P.vertices.values.length = D := by
    simpa only [Fintype.card_fin] using P.vertices.length_eq_card
  have hl : P.leftovers.length ≤ P.vertices.values.length := List.length_filter_le _ _
  exact (List.idxOf_le_length.trans hl).trans_eq hlen

theorem volume_le {D : ℕ} {U : Type*} [DecidableEq U]
    (P : PackingData (Fin D) U) (encodeType : U → List Bool) (a : Data)
    (htable : a.stacks 265 = SubexpGlobalRowPacking.table P encodeType) (v : Fin D) :
    SubexpGlobalRowPacking.volume P encodeType v ≤ (a.stacks 265).length + D + 1 := by
  unfold SubexpGlobalRowPacking.volume Subexp.GlobalBasisMetadata.volume
  change (SubexpGlobalRowPacking.table P encodeType).length +
    (SubexpGlobalRowPacking.key v).length + 1 ≤ _
  rw [← htable]
  simp only [SubexpGlobalRowPacking.key, unary, List.length_replicate]
  have := v.isLt
  omega

/-- Every row branch returns one target-width array of `R+1` quartets. -/
def rowLength (p μ R : ℕ) : ℕ := (R + 1) * (4 * baseWidth p μ)

variable {p r Q Δ D : ℕ} [Fact p.Prime]
variable (μ : ℕ) (source : SubexpSelectedConversions.Prepared p 0)
variable (xs : List (ZMod p)) (inverse negative : Fin Q → List Bool)
  (difference : Fin Q → Fin Q → List Bool)
variable (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))

theorem outputAt_length (i : Fin Δ) (v w : Fin D) :
    (SubexpGlobalRowService.outputAt μ source xs inverse negative difference P i v w).length =
      rowLength p μ xs.length := by
  unfold SubexpGlobalRowService.outputAt
  cases P.lookup v with
  | none => exact SubexpGlobalRowConstants.output_length μ source xs.length _
  | some z =>
      rcases z with ⟨block, u⟩
      cases P.lookup w with
      | none => exact SubexpGlobalRowConstants.output_length μ source xs.length _
      | some z =>
          rcases z with ⟨other, y⟩
          dsimp only
          split_ifs
          · exact SubexpGlobalRowValues.output_length source i u y xs inverse negative difference μ
          · exact SubexpGlobalRowConstants.output_length μ source xs.length _

theorem render_length_le (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ) (e v w : ℕ) :
    (SubexpDenseRowProducer.render μ source xs inverse negative difference P scopes hd e v w).length ≤
      rowLength p μ xs.length := by
  unfold SubexpDenseRowProducer.render
  split_ifs <;> simp only [List.length_reverse, outputAt_length, List.length_nil, Nat.zero_le, le_refl]

theorem evaluator_mono (R b B L K : ℕ) (h : L ≤ K) :
    SubexpRowToTaylor.runtimeBound R b B L ≤ SubexpRowToTaylor.runtimeBound R b B K := by
  unfold SubexpRowToTaylor.runtimeBound
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _) _) _

/-- Explicit cost of both metadata lookups, prefix-slot scan and constant
emission. `T` is the fixed type-code width; `L` is the stored lookup length. -/
def dispatchBound (D T b L S E : ℕ) : ℕ :=
  800 * (L + D + 1)^2 + 1000 * (S + E + D + 1)^2 + 64 * D + 4 * T + 56 * b + 200

/-- The source and source-code limits are supplied by the concrete universal
builder estimates below. The extra constant covers every dispatch branch. -/
def serviceBound (D T R b B L S E sourceLimit codeLimit : ℕ) : ℕ :=
  3 * (dispatchBound D T b L S E + sourceLimit) + 68 +
    SubexpRowToTaylor.runtimeBound R b B (codeLimit + 8 * b + 2)

omit [Fact p.Prime] in
theorem classifyCost_le (scopes : List (List ℕ)) (e : ℕ) (he : e ≤ scopes.length)
    (a : Data) (htable : a.stacks 265 =
      SubexpGlobalRowPacking.table P Subexp.CollisionProgram.encodeType)
    (v w : Fin D) (block : Fin P.blockCount) :
    SubexpGlobalRowUniversal.classifyCost P scopes e v w block ≤
      dispatchBound D (Subexp.CollisionProgram.typeWidth r Q Δ) (baseWidth p 1)
        (a.stacks 265).length (SubexpIncidenceSlotProgram.scopeBits scopes).length scopes.length := by
  have hv := Nat.pow_le_pow_left (volume_le P Subexp.CollisionProgram.encodeType a htable v) 2
  have hw := Nat.pow_le_pow_left (volume_le P Subexp.CollisionProgram.encodeType a htable w) 2
  have hb : block.val ≤ D := (Nat.le_of_lt block.isLt).trans (blockCount_le P)
  have hvD : v.val ≤ D := Nat.le_of_lt v.isLt
  have hs := SubexpIncidenceSlotProgram.budget_le scopes e v.val
    ((SubexpIncidenceSlotProgram.scopeBits scopes).length + scopes.length + D)
    (by omega) (by omega) (by omega)
  unfold SubexpGlobalRowUniversal.classifyCost dispatchBound
  omega

theorem costAt_le (scopes : List (List ℕ)) (e : ℕ) (he : e ≤ scopes.length)
    (a : Data) (htable : a.stacks 265 =
      SubexpGlobalRowPacking.table P Subexp.CollisionProgram.encodeType)
    (sourceLimit codeLimit : ℕ)
    (hs : ∀ (i : Fin Δ) (u y : MulticolorTypes.UniversalType r Q Δ),
      SubexpGlobalRowUniversal.sourceCost xs inverse negative difference a i u y ≤ sourceLimit)
    (hc : ∀ (i : Fin Δ) (u y : MulticolorTypes.UniversalType r Q Δ),
      (SubexpRowToTaylorCalls.code
        (SubexpGlobalRowValues.expression source i u y xs inverse negative difference)).length ≤ codeLimit)
    (i : Fin Δ) (v w : Fin D) :
    SubexpGlobalRowService.costAt μ source xs inverse negative difference P scopes e a i v w ≤
      serviceBound D (Subexp.CollisionProgram.typeWidth r Q Δ) xs.length
        (baseWidth p 1) (baseWidth p μ) (a.stacks 265).length
        (SubexpIncidenceSlotProgram.scopeBits scopes).length scopes.length sourceLimit codeLimit := by
  have hv := Nat.pow_le_pow_left (volume_le P Subexp.CollisionProgram.encodeType a htable v) 2
  have hw := Nat.pow_le_pow_left (volume_le P Subexp.CollisionProgram.encodeType a htable w) 2
  have hvi := leftover_index_le P v
  have hwi := leftover_index_le P w
  have hvD : v.val ≤ D := Nat.le_of_lt v.isLt
  have hwD : w.val ≤ D := Nat.le_of_lt w.isLt
  have heval := evaluator_mono xs.length (baseWidth p 1) (baseWidth p μ)
    (8 * baseWidth p 1 + 2) (codeLimit + 8 * baseWidth p 1 + 2) (by omega)
  cases hlookupv : P.lookup v with
  | none =>
      have hbase :
          400 * (SubexpGlobalRowPacking.volume P Subexp.CollisionProgram.encodeType v)^2 +
          18 * v.val + 9 * w.val + 14 * (4 * baseWidth p 1) + 2 * P.leftovers.idxOf v + 99 ≤
          dispatchBound D (Subexp.CollisionProgram.typeWidth r Q Δ) (baseWidth p 1)
            (a.stacks 265).length (SubexpIncidenceSlotProgram.scopeBits scopes).length scopes.length := by
        unfold dispatchBound
        omega
      simp only [SubexpGlobalRowService.costAt, hlookupv, SubexpGlobalRowConstants.evaluationCost_eq]
      unfold serviceBound
      omega
  | some z =>
      rcases z with ⟨block, u⟩
      have hblock : block.val ≤ D := (Nat.le_of_lt block.isLt).trans (blockCount_le P)
      cases hlookupw : P.lookup w with
      | none =>
          have hbase :
              400 * (SubexpGlobalRowPacking.volume P Subexp.CollisionProgram.encodeType v)^2 +
              400 * (SubexpGlobalRowPacking.volume P Subexp.CollisionProgram.encodeType w)^2 +
              14 * (4 * baseWidth p 1) +
              2 * (block.val + (Subexp.CollisionProgram.encodeType u).length + P.leftovers.idxOf w) + 75 ≤
              dispatchBound D (Subexp.CollisionProgram.typeWidth r Q Δ) (baseWidth p 1)
                (a.stacks 265).length (SubexpIncidenceSlotProgram.scopeBits scopes).length scopes.length := by
            simp only [Subexp.CollisionProgram.encodeType_length]
            unfold dispatchBound
            omega
          simp only [SubexpGlobalRowService.costAt, hlookupv, hlookupw,
            SubexpGlobalRowConstants.evaluationCost_eq]
          unfold serviceBound
          omega
      | some z =>
          rcases z with ⟨other, y⟩
          have hother : other.val ≤ D := (Nat.le_of_lt other.isLt).trans (blockCount_le P)
          by_cases hsame : block = other
          · have hclass := classifyCost_le (p := p) P scopes e he a htable v w block
            have hsource := hs i u y
            have hcode := evaluator_mono xs.length (baseWidth p 1) (baseWidth p μ) _
              (codeLimit + 8 * baseWidth p 1 + 2) ((hc i u y).trans (by omega))
            simp only [SubexpGlobalRowService.costAt, hlookupv, hlookupw, ite_eq_left hsame]
            unfold serviceBound
            omega
          · have hbase :
                400 * (SubexpGlobalRowPacking.volume P Subexp.CollisionProgram.encodeType v)^2 +
                400 * (SubexpGlobalRowPacking.volume P Subexp.CollisionProgram.encodeType w)^2 +
                18 * block.val + 9 * other.val + 14 * (4 * baseWidth p 1) +
                2 * (block.val + (Subexp.CollisionProgram.encodeType u).length +
                  other.val + (Subexp.CollisionProgram.encodeType y).length) + 101 ≤
                dispatchBound D (Subexp.CollisionProgram.typeWidth r Q Δ) (baseWidth p 1)
                  (a.stacks 265).length (SubexpIncidenceSlotProgram.scopeBits scopes).length scopes.length := by
              simp only [Subexp.CollisionProgram.encodeType_length]
              unfold dispatchBound
              omega
            simp only [SubexpGlobalRowService.costAt, hlookupv, hlookupw, ite_eq_right hsame,
              SubexpGlobalRowConstants.evaluationCost_eq]
            unfold serviceBound
            omega

omit [Fact p.Prime] in
/-- The metadata update used in the numerical source bound satisfies the
  same physical input contract as the actual classifier output. -/
theorem staged_prepared (a : Data)
    (hm : SubexpGlobalRowInputs.Masters p r Q xs inverse negative difference a)
    (i : Fin Δ) (u y : MulticolorTypes.UniversalType r Q Δ) :
    Subexp.UniversalRowAssembly.PreparedInput p i u y xs inverse negative difference
      (SubexpGlobalRowUniversal.inner (SubexpGlobalRowUniversal.staged a i u y)) := by
  apply SubexpGlobalRowInputs.Masters.prepared p r Q xs inverse negative difference i u y hm
  · intro j hj
    have h272 : j ≠ 272 := by
      intro h
      subst j
      exact hj (by decide)
    have h275 : j ≠ 275 := by
      intro h
      subst j
      exact hj (by decide)
    have h284 : j ≠ 284 := by
      intro h
      subst j
      exact hj (by decide)
    simp [SubexpGlobalRowUniversal.staged, h272, h275, h284]
  · simp [SubexpGlobalRowUniversal.staged]
  · simp [SubexpGlobalRowUniversal.staged]
  · simp [SubexpGlobalRowUniversal.staged, unary]

/-- Code bytes are paid for by the actual source-generation run. This
avoids any independently assumed bound on a represented expression. -/
theorem code_length_le_sourceCost (a : Data) (h2 : (2 : ZMod p) ≠ 0)
    (hm : SubexpGlobalRowInputs.Masters p r Q xs inverse negative difference a)
    (hzero : a.stacks 131 = SubexpFlatAdd.encode source.zero)
    (hone : a.stacks 132 = SubexpFlatAdd.encode source.one)
    (i : Fin Δ) (u y : MulticolorTypes.UniversalType r Q Δ) :
    (SubexpRowToTaylorCalls.code
      (SubexpGlobalRowValues.expression source i u y xs inverse negative difference)).length ≤
        SubexpGlobalRowUniversal.sourceCost xs inverse negative difference a i u y := by
  let staged := SubexpGlobalRowUniversal.inner (SubexpGlobalRowUniversal.staged a i u y)
  have hp := staged_prepared xs inverse negative difference a hm i u y
  obtain ⟨b, hr, hs⟩ := Subexp.UniversalRowAssembly.program_runsIn_prepared
    p i u y xs h2 inverse negative difference staged hp
  have hg := BitProgram.runsIn_listStackBits Subexp.UniversalRowAssembly.program [26]
    (by simp) hr
  change (b.stacks 26).length + 0 ≤ (staged.stacks 26).length + 0 + _ at hg
  rw [hs, Function.update_self, hp.code] at hg
  have hz : staged.stacks 131 = SubexpFlatAdd.encode source.zero := by
    simpa [staged, SubexpGlobalRowUniversal.inner, projectState,
      SubexpGlobalRowUniversal.staged] using hzero
  have ho : staged.stacks 132 = SubexpFlatAdd.encode source.one := by
    simpa [staged, SubexpGlobalRowUniversal.inner, projectState,
      SubexpGlobalRowUniversal.staged] using hone
  rw [SubexpGlobalRowValues.sourceWord_eq_code source i u y xs inverse negative difference
    hm.inverseWidth hm.negativeWidth hm.differenceWidth staged hz ho] at hg
  simpa only [List.length_nil, Nat.zero_add, Nat.add_zero,
    SubexpGlobalRowUniversal.sourceCost] using hg

/-- Uniform service budget after the actual source-cost estimate has
been discharged. The same bound pays for every emitted code byte. -/
def uniformRowBound (p r Q Δ D μ : ℕ) (R sourceLimit : ℕ)
    (scopes : List (List ℕ)) (a : Data) : ℕ :=
  serviceBound D (Subexp.CollisionProgram.typeWidth r Q Δ) R
    (baseWidth p 1) (baseWidth p μ) (a.stacks 265).length
    (SubexpIncidenceSlotProgram.scopeBits scopes).length scopes.length sourceLimit sourceLimit

theorem rowCost_le_of_sourceBound (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (a : Data) (h2 : (2 : ZMod p) ≠ 0)
    (hm : SubexpGlobalRowInputs.Masters p r Q xs inverse negative difference a)
    (htable : a.stacks 265 = SubexpGlobalRowPacking.table P Subexp.CollisionProgram.encodeType)
    (hzero : a.stacks 131 = SubexpFlatAdd.encode source.zero)
    (hone : a.stacks 132 = SubexpFlatAdd.encode source.one)
    (sourceLimit : ℕ)
    (hs : ∀ (i : Fin Δ) (u y : MulticolorTypes.UniversalType r Q Δ),
      SubexpGlobalRowUniversal.sourceCost xs inverse negative difference a i u y ≤ sourceLimit)
    (e v w : ℕ) :
    SubexpDenseRowProducer.rowCost μ source xs inverse negative difference P scopes hd a e v w ≤
      uniformRowBound p r Q Δ D μ xs.length sourceLimit scopes a := by
  have hc (i : Fin Δ) (u y : MulticolorTypes.UniversalType r Q Δ) :
      (SubexpRowToTaylorCalls.code
        (SubexpGlobalRowValues.expression source i u y xs inverse negative difference)).length ≤ sourceLimit :=
    (code_length_le_sourceCost source xs inverse negative difference a h2 hm hzero hone i u y).trans
      (hs i u y)
  unfold SubexpDenseRowProducer.rowCost
  split_ifs with he hv hw hm'
  · exact costAt_le μ source xs inverse negative difference P scopes e he.le a htable
      sourceLimit sourceLimit hs hc _ _ _
  all_goals exact Nat.zero_le _

theorem rowBounds_of_sourceBound (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (a : Data) (h2 : (2 : ZMod p) ≠ 0)
    (hm : SubexpGlobalRowInputs.Masters p r Q xs inverse negative difference a)
    (htable : a.stacks 265 = SubexpGlobalRowPacking.table P Subexp.CollisionProgram.encodeType)
    (hzero : a.stacks 131 = SubexpFlatAdd.encode source.zero)
    (hone : a.stacks 132 = SubexpFlatAdd.encode source.one)
    (sourceLimit : ℕ)
    (hs : ∀ (i : Fin Δ) (u y : MulticolorTypes.UniversalType r Q Δ),
      SubexpGlobalRowUniversal.sourceCost xs inverse negative difference a i u y ≤ sourceLimit) :
    RowBounds (SubexpDenseRowProducer.render μ source xs inverse negative difference P scopes hd)
      (SubexpDenseRowProducer.rowCost μ source xs inverse negative difference P scopes hd a)
      D (uniformRowBound p r Q Δ D μ xs.length sourceLimit scopes a)
      (rowLength p μ xs.length) 0 scopes := by
  have hall (e v w : ℕ) := rowCost_le_of_sourceBound μ source xs inverse negative difference P
    scopes hd a h2 hm htable hzero hone sourceLimit hs e v w
  have hrec (remaining : List (List ℕ)) (e : ℕ) :
      RowBounds (SubexpDenseRowProducer.render μ source xs inverse negative difference P scopes hd)
        (SubexpDenseRowProducer.rowCost μ source xs inverse negative difference P scopes hd a)
        D (uniformRowBound p r Q Δ D μ xs.length sourceLimit scopes a)
        (rowLength p μ xs.length) e remaining := by
    induction remaining generalizing e with
    | nil => trivial
    | cons vertices rest ih =>
        refine ⟨?_, ih (e + 1)⟩
        intro v hv w hw
        exact ⟨hall e v w, render_length_le μ source xs inverse negative difference P scopes hd e v w⟩
  exact hrec scopes 0

end SubexponentialSAT.SubexpDenseRowServiceBound

end OAI.Algorithms
