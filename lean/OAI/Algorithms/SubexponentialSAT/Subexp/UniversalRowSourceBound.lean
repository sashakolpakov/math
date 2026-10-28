import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowAssemblyPrepared

namespace OAI.Algorithms

/-! Polynomial bounds for the actual nested row-data and source emitters. -/

namespace SubexponentialSAT.Subexp.UniversalRowSourceBound

open UniversalRowProgram
open UniversalRowFactorLoop (indexWord)

abbrev Word := List Bool

def indicesBound (S : ℕ) := 1 + (2 * S + 2) * S
def factorBytes (S : ℕ) := 4 * S + 2
def factorsBytes (S : ℕ) := 1 + (2 * factorBytes S + 2) * S
def termBytes (S : ℕ) := 4 * S + 2 + factorsBytes S
def rowBytes (S : ℕ) := 2 * S + 2 + (2 * termBytes S + 2) * S
def inputBound (S : ℕ) := 2 * S + rowBytes S + 1
def factorCallbackBound (S : ℕ) := (28 * S + 60) * S + 9 * S + 80 * S + 140
def factorLoopBound (S : ℕ) := S * (6 * S + factorCallbackBound S + 7)
def termBound (S : ℕ) :=
  S * (28 * S + 14 * S + 51) + 30 * S + 15 * S + 63 +
    7 * indicesBound S + factorLoopBound S +
    (24 * (S + S) + 8 * factorsBytes S + 42) + 2 * S + 2 * S + 20
def outerLoopBound (S : ℕ) := S * (6 * S + termBound S + 7)
def dataBound (S : ℕ) :=
  10 * indicesBound S + 13 * S + 6 * S + 40 +
    (7 * indicesBound S + 8 + outerLoopBound S) + 8 * S + 11
def sourceBound (S : ℕ) := dataBound S + 2048 * inputBound S ^ 2 + 4
def sourceLengthBound (S : ℕ) := 300 * inputBound S ^ 2

theorem getD_length_le (xs : List Word) (S : ℕ)
    (h : ∀ x ∈ xs, x.length ≤ S) (i : ℕ) : (xs.getD i []).length ≤ S := by
  by_cases hi : i < xs.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

theorem record_budget_le (cost : Word → ℕ) (records : List Word) (S C : ℕ)
    (hsize : ∀ w ∈ records, w.length ≤ S) (hcost : ∀ w ∈ records, cost w ≤ C) :
    RecordPrograms.budget cost records ≤ records.length * (6 * S + C + 7) := by
  induction records with
  | nil => simp [RecordPrograms.budget]
  | cons w ws ih =>
      have hw := hsize w (by simp)
      have hc := hcost w (by simp)
      have ht := ih (fun x hx => hsize x (by simp [hx]))
        (fun x hx => hcost x (by simp [hx]))
      simp only [RecordPrograms.budget, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem index_records_size (positions : List ℕ) (S : ℕ)
    (hpos : ∀ i ∈ positions, i ≤ S) :
    ∀ w ∈ positions.reverse.map indexWord, w.length ≤ S := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  simpa only [UniversalRowFactorLoop.indexWord_length] using
    hpos i (List.mem_reverse.mp hi)

theorem indices_length_le (positions : List ℕ) (S : ℕ)
    (hlen : positions.length ≤ S) (hpos : ∀ i ∈ positions, i ≤ S) :
    (UniversalRowTermProgram.indices positions).length ≤ indicesBound S := by
  have h := Encoding.length_encodeList_upper id (positions.reverse.map indexWord) S
    (index_records_size positions S hpos)
  simp only [List.length_map, List.length_reverse] at h
  exact h.trans (by unfold indicesBound; gcongr)

theorem factor_length_le (differences negatives : List Word) (S j : ℕ)
    (hd : ∀ x ∈ differences, x.length ≤ S) (hn : ∀ x ∈ negatives, x.length ≤ S) :
    (encodeFactor (UniversalRowFactorLoop.factor differences negatives j)).length ≤ factorBytes S := by
  have h1 := getD_length_le differences S hd j
  have h2 := getD_length_le negatives S hn j
  simp only [encodeFactor, UniversalRowFactorLoop.factor, List.length_append, Encoding.length_frame]
  unfold factorBytes
  omega

theorem factors_length_le (differences negatives : List Word) (positions : List ℕ) (S i : ℕ)
    (hlen : positions.length ≤ S)
    (hd : ∀ x ∈ differences, x.length ≤ S) (hn : ∀ x ∈ negatives, x.length ≤ S) :
    (Encoding.encodeList encodeFactor
      (UniversalRowFactorLoop.factors differences negatives i positions)).length ≤ factorsBytes S := by
  have hc : (UniversalRowFactorLoop.factors differences negatives i positions).length ≤ S := by
    simpa only [UniversalRowFactorLoop.factors, List.length_map] using
      (List.length_filter_le (fun j => decide (j ≠ i)) positions).trans hlen
  have h := Encoding.length_encodeList_upper encodeFactor
    (UniversalRowFactorLoop.factors differences negatives i positions) (factorBytes S) (by
      intro f hf
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hf
      exact factor_length_le differences negatives S j hd hn)
  exact h.trans (by unfold factorsBytes; gcongr)

theorem term_length_le (t : UniversalRowLoop.Tables) (positions : List ℕ) (S i : ℕ)
    (hlen : positions.length ≤ S)
    (hv : ∀ x ∈ t.values, x.length ≤ S) (hi : ∀ x ∈ t.inverses, x.length ≤ S)
    (hn : ∀ x ∈ t.negatives, x.length ≤ S)
    (hd : ∀ x ∈ t.differences.getD i [], x.length ≤ S) :
    (encodeTerm (UniversalRowLoop.term t positions i)).length ≤ termBytes S := by
  have h1 := getD_length_le t.values S hv i
  have h2 := getD_length_le t.inverses S hi i
  have h3 := factors_length_le (t.differences.getD i []) t.negatives positions S i hlen hd hn
  simp only [encodeTerm, UniversalRowLoop.term, UniversalRowTermProgram.term,
    List.length_append, Encoding.length_frame]
  unfold termBytes
  omega

theorem row_length_le (t : UniversalRowLoop.Tables) (positions : List ℕ) (delta limit : Word)
    (S : ℕ) (hlen : positions.length ≤ S) (hdelta : delta.length ≤ S)
    (hterm : ∀ i ∈ positions, (encodeTerm (UniversalRowLoop.term t positions i)).length ≤ termBytes S) :
    (encodeRow (UniversalRowDataProgram.row t positions delta limit)).length ≤ rowBytes S := by
  have hc : (UniversalRowDataProgram.row t positions delta limit).terms.length ≤ S := by
    simp only [UniversalRowDataProgram.row]
    split_ifs <;> simp_all
  have h := Encoding.length_encodeList_upper encodeTerm
    (UniversalRowDataProgram.row t positions delta limit).terms (termBytes S) (by
      intro term ht
      simp only [UniversalRowDataProgram.row] at ht
      split_ifs at ht with hguard
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
        exact hterm i hi
      · simp at ht)
  simp only [encodeRow, List.length_append, Encoding.length_frame]
  change 2 * delta.length + 1 + _ ≤ _
  have hh := h.trans (show 1 + (2 * termBytes S + 2) * _ ≤
      1 + (2 * termBytes S + 2) * S by gcongr)
  unfold rowBytes
  omega

theorem term_cost_le (t : UniversalRowLoop.Tables) (width rowWidth : Word)
    (positions : List ℕ) (S i : ℕ) (hlen : positions.length ≤ S)
    (hpos : ∀ j ∈ positions, j ≤ S) (hi : i ≤ S)
    (hw : width.length ≤ S) (hr : rowWidth.length ≤ S)
    (hv : ∀ x ∈ t.values, x.length ≤ S) (hinv : ∀ x ∈ t.inverses, x.length ≤ S)
    (hn : ∀ x ∈ t.negatives, x.length ≤ S)
    (hd : ∀ x ∈ t.differences.getD i [], x.length ≤ S) :
    UniversalRowTermProgram.cost t.values t.inverses t.negatives (t.differences.getD i [])
      width rowWidth positions i ≤ termBound S := by
  have hindices := indices_length_le positions S hlen hpos
  have hrecords := index_records_size positions S hpos
  have hcallback : ∀ w ∈ positions.reverse.map indexWord,
      UniversalRowFactorLoop.callbackCost width.length i w ≤ factorCallbackBound S := by
    intro w hwmem
    have hwl := hrecords w hwmem
    unfold UniversalRowFactorLoop.callbackCost factorCallbackBound
    gcongr
  have hloop := record_budget_le (UniversalRowFactorLoop.callbackCost width.length i)
    (positions.reverse.map indexWord) S (factorCallbackBound S) hrecords hcallback
  simp only [List.length_map, List.length_reverse] at hloop
  have hl : RecordPrograms.budget (UniversalRowFactorLoop.callbackCost width.length i)
      (positions.reverse.map indexWord) ≤ factorLoopBound S :=
    hloop.trans (by unfold factorLoopBound; gcongr)
  have hv' := getD_length_le t.values S hv i
  have hi' := getD_length_le t.inverses S hinv i
  have hf := factors_length_le (t.differences.getD i []) t.negatives positions S i hlen hd hn
  unfold UniversalRowTermProgram.cost UniversalRowTermFraming.termCost termBound
  gcongr

theorem source_bound_le (t : UniversalRowLoop.Tables) (width rowWidth : Word)
    (positions : List ℕ) (delta limit zero one : Word) (S : ℕ)
    (valid : UniversalRowLoop.Valid t width rowWidth positions)
    (hlen : positions.length ≤ S) (hpos : ∀ i ∈ positions, i ≤ S)
    (hw : width.length ≤ S) (hr : rowWidth.length ≤ S)
    (hd : delta.length ≤ S) (hl : limit.length ≤ S)
    (hz : zero.length ≤ S) (ho : one.length ≤ S) :
    UniversalRowSourceProgram.bound t width rowWidth positions delta limit zero one ≤ sourceBound S ∧
      (rowCode zero one (zero ++ one) (UniversalRowDataProgram.row t positions delta limit)).length ≤
        sourceLengthBound S := by
  have hv : ∀ x ∈ t.values, x.length ≤ S := fun x hx => (valid.values x hx).le.trans hw
  have hinv : ∀ x ∈ t.inverses, x.length ≤ S := fun x hx => (valid.inverses x hx).le.trans hw
  have hn : ∀ x ∈ t.negatives, x.length ≤ S := fun x hx => (valid.negatives x hx).le.trans hw
  have hdiff (i : ℕ) (hi : i ∈ positions) : ∀ x ∈ t.differences.getD i [], x.length ≤ S :=
    fun x hx => (valid.differences i hi x hx).le.trans hw
  have hterms : ∀ i ∈ positions, (encodeTerm (UniversalRowLoop.term t positions i)).length ≤ termBytes S :=
    fun i hi => term_length_le t positions S i hlen hv hinv hn (hdiff i hi)
  have hrow := row_length_le t positions delta limit S hlen hd hterms
  have hinput : inputSize zero one (UniversalRowDataProgram.row t positions delta limit) ≤ inputBound S := by
    unfold inputSize inputBound
    omega
  have hrecords := index_records_size positions S hpos
  have houter := record_budget_le (UniversalRowLoop.cost t width rowWidth positions)
    (positions.reverse.map indexWord) S (termBound S) hrecords (by
      intro w hwmem
      obtain ⟨i, himem, rfl⟩ := List.mem_map.mp hwmem
      have hip := List.mem_reverse.mp himem
      simpa only [UniversalRowLoop.cost, UniversalRowFactorLoop.indexWord_length] using
        term_cost_le t width rowWidth positions S i hlen hpos (hpos i hip) hw hr hv hinv hn (hdiff i hip))
  simp only [List.length_map, List.length_reverse] at houter
  have hout : RecordPrograms.budget (UniversalRowLoop.cost t width rowWidth positions)
      (positions.reverse.map indexWord) ≤ outerLoopBound S :=
    houter.trans (by unfold outerLoopBound; gcongr)
  have hindices := indices_length_le positions S hlen hpos
  have hdata : UniversalRowDataProgram.cost t width rowWidth positions delta limit ≤ dataBound S := by
    unfold UniversalRowDataProgram.cost UniversalRowDataProgram.activeCost dataBound
    gcongr
  constructor
  · unfold UniversalRowSourceProgram.bound sourceBound
    gcongr
  · exact (rowCode_length_le zero one (zero ++ one) _).trans
      ((rowCost_quadratic zero one _).trans (by unfold sourceLengthBound; gcongr))

end SubexponentialSAT.Subexp.UniversalRowSourceBound

end OAI.Algorithms
