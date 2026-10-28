import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSource
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowDataProgram

namespace OAI.Algorithms

/-!
# Indexed cache tables and the represented interpolation row

The physical producer reads natural-number indexed lists. This adapter
identifies those reads with the finite-indexed row specification, including
the mismatch filter and the cardinality guard. Its premises concern only
individual input cache entries, the delta word, and the limit's length.
-/

namespace SubexponentialSAT.Subexp.UniversalRowTableSource

open SubexpSymbolicCost SubexpRepresentedRows SubexpRowInterpolation
open UniversalRowSource
open UniversalRowProgram (Row rowExpression)

variable {C E A B : Type*} {Q : ℕ}

def positions (s : Finset (Fin Q)) : List ℕ :=
  (UniversalRowSource.selected s).map Fin.val

theorem positions_mismatch {V G : Type*} [DecidableEq G]
    (head : V → Fin Q → G) (σ : Fin Q → G) (y : V) :
    positions (mismatchPositions head σ y) =
      ((List.finRange Q).filter (fun i => decide (head y i ≠ σ i))).map Fin.val := by
  simp [positions, UniversalRowSource.selected]

@[simp] theorem positions_length (s : Finset (Fin Q)) :
    (positions s).length = s.card := by
  rw [positions, List.length_map,
    ← List.toFinset_card_of_nodup (UniversalRowSource.selected_nodup s), selected_toFinset]

theorem positions_filter (s : Finset (Fin Q)) (i : Fin Q) :
    (positions s).filter (fun j => decide (j ≠ i.val)) = positions (s.erase i) := by
  unfold positions UniversalRowSource.selected
  rw [List.filter_map, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro j _
  simp [ Fin.val_injective.eq_iff]

theorem mapRow_comp (f : C → A) (g : A → B) (row : Row C) :
    mapRow g (mapRow f row) = mapRow (g ∘ f) row := by
  cases row
  simp [mapRow, mapTerm, mapFactor, List.map_map, Function.comp_def]

variable (ops : RingProgram C) (cache : NodeCache C Q) (encode : C → List Bool)
variable (t : UniversalRowLoop.Tables)

theorem factors_eq (s : Finset (Fin Q)) (i : Fin Q)
    (hdifference : ∀ j : Fin Q,
      (t.differences.getD i.val []).getD j.val [] = encode (cache.difference i j))
    (hnegative : ∀ j : Fin Q,
      t.negatives.getD j.val [] = encode ((ops.negRun (cache.node j)).1)) :
    UniversalRowFactorLoop.factors (t.differences.getD i.val []) t.negatives
        i.val (positions s) =
      (UniversalRowSource.selected (s.erase i)).map
        (fun j => mapFactor encode (factorData ops cache i j)) := by
  unfold UniversalRowFactorLoop.factors
  rw [positions_filter, positions, List.map_map]
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_def, UniversalRowFactorLoop.factor, hdifference, hnegative,
    mapFactor, factorData]

theorem term_eq (s : Finset (Fin Q)) (d : Fin Q → C) (i : Fin Q)
    (hvalue : t.values.getD i.val [] = encode (d i))
    (hinverse : t.inverses.getD i.val [] = encode (cache.inverse i))
    (hdifference : ∀ j : Fin Q,
      (t.differences.getD i.val []).getD j.val [] = encode (cache.difference i j))
    (hnegative : ∀ j : Fin Q,
      t.negatives.getD j.val [] = encode ((ops.negRun (cache.node j)).1)) :
    UniversalRowLoop.term t (positions s) i.val =
      mapTerm encode (termData ops cache s d i) := by
  simp only [UniversalRowLoop.term, UniversalRowTermProgram.term, mapTerm, termData,
    List.map_map]
  rw [hvalue, hinverse, factors_eq ops cache encode t s i hdifference hnegative]
  rfl

/-- The actual count guard and filtered natural-index reads produce the
same row record as the finite-indexed represented construction. -/
theorem row_eq {V G : Type*} [Fintype V] [DecidableEq V] [DecidableEq G]
    (v : V) (head : V → Fin Q → G) (σ : Fin Q → G) (R : ℕ)
    (d : V → Fin Q → C) (y : V) (delta limit : List Bool)
    (hvalue : ∀ i : Fin Q, t.values.getD i.val [] = encode (d y i))
    (hinverse : ∀ i : Fin Q, t.inverses.getD i.val [] = encode (cache.inverse i))
    (hdifference : ∀ i j : Fin Q,
      (t.differences.getD i.val []).getD j.val [] = encode (cache.difference i j))
    (hnegative : ∀ j : Fin Q,
      t.negatives.getD j.val [] = encode ((ops.negRun (cache.node j)).1))
    (hdelta : delta = encode (if v = y then ops.oneRun.1 else ops.zeroRun.1))
    (hlimit : limit.length = R) :
    UniversalRowDataProgram.row t (positions (mismatchPositions head σ y)) delta limit =
      mapRow encode (rowData ops cache v head σ R d y) := by
  simp only [UniversalRowDataProgram.row, mapRow, rowData, positions_length, hlimit, hdelta]
  by_cases h : (mismatchPositions head σ y).card ≤ R
  · have hy : y ∈ correctionColumns head σ R := (mem_correctionColumns head σ R y).mpr h
    simp only [ite_eq_left h, ite_eq_left hy, positions, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro i _
    exact term_eq ops cache encode t _ (d y) i (hvalue i) (hinverse i)
      (hdifference i) hnegative
  · have hy : y ∉ correctionColumns head σ R := by
      simpa only [mem_correctionColumns] using h
    simp [h, hy]

/-- Decoding the physical row record gives the full represented row
polynomial. Only local input-cache and scalar-decoder laws are assumed. -/
theorem row_eval [CommRing E] (source : RepresentedRing C E)
    {node : Fin Q → E} (units : NodeUnits node)
    (hnode : ∀ i, source.decode (cache.node i) = node i)
    (hinv : ∀ i, source.decode (cache.inverse i) = units.nodeInverse i)
    (hdiff : ∀ i j, source.decode (cache.difference i j) = units.differenceInverse i j)
    (decode : List Bool → E) (hdecode : ∀ x, decode (encode x) = source.decode x)
    {V G : Type*} [Fintype V] [DecidableEq V] [DecidableEq G]
    (v : V) (head : V → Fin Q → G) (σ : Fin Q → G) (R : ℕ)
    (d : V → Fin Q → C) (y : V) (delta limit : List Bool)
    (hvalue : ∀ i : Fin Q, t.values.getD i.val [] = encode (d y i))
    (hinverse : ∀ i : Fin Q, t.inverses.getD i.val [] = encode (cache.inverse i))
    (hdifference : ∀ i j : Fin Q,
      (t.differences.getD i.val []).getD j.val [] = encode (cache.difference i j))
    (hnegative : ∀ j : Fin Q,
      t.negatives.getD j.val [] = encode ((source.negRun (cache.node j)).1))
    (hdelta : delta = encode (if v = y then source.oneRun.1 else source.zeroRun.1))
    (hlimit : limit.length = R) :
    (rowExpression Polynomial.X (mapRow (fun bits => Polynomial.C (decode bits))
      (UniversalRowDataProgram.row t (positions (mismatchPositions head σ y)) delta limit))).eval =
      (SubexpTaylorExecution.mapCode source.decode
        (SubexpRepresentedRows.row source.program cache v head σ R d y)).denote := by
  rw [row_eq source.program cache encode t v head σ R d y delta limit
    hvalue hinverse hdifference hnegative hdelta hlimit, mapRow_comp]
  have hmap : (fun bits => Polynomial.C (decode bits)) ∘ encode =
      fun x => Polynomial.C (source.decode x) := by
    funext x
    simp only [Function.comp_apply, hdecode]
  rw [hmap]
  exact rowData_eval source cache units hnode hinv hdiff v head σ R d y

/-- Individual cache words may use any valid representation of their
scalars. No equality of the raw representatives is needed. -/
theorem map_factors_eq (decode : List Bool → A) (decodeC : C → A)
    (s : Finset (Fin Q)) (i : Fin Q)
    (hdifference : ∀ j : Fin Q, decode ((t.differences.getD i.val []).getD j.val []) =
      decodeC (cache.difference i j))
    (hnegative : ∀ j : Fin Q, decode (t.negatives.getD j.val []) =
      decodeC ((ops.negRun (cache.node j)).1)) :
    (UniversalRowFactorLoop.factors (t.differences.getD i.val []) t.negatives
      i.val (positions s)).map (mapFactor decode) =
      (UniversalRowSource.selected (s.erase i)).map
        (fun j => mapFactor decodeC (factorData ops cache i j)) := by
  unfold UniversalRowFactorLoop.factors
  rw [positions_filter, positions]
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro j _
  simp only [mapFactor, UniversalRowFactorLoop.factor, factorData, hdifference, hnegative]

theorem map_term_eq (decode : List Bool → A) (decodeC : C → A)
    (s : Finset (Fin Q)) (d : Fin Q → C) (i : Fin Q)
    (hvalue : decode (t.values.getD i.val []) = decodeC (d i))
    (hinverse : decode (t.inverses.getD i.val []) = decodeC (cache.inverse i))
    (hdifference : ∀ j : Fin Q, decode ((t.differences.getD i.val []).getD j.val []) =
      decodeC (cache.difference i j))
    (hnegative : ∀ j : Fin Q, decode (t.negatives.getD j.val []) =
      decodeC ((ops.negRun (cache.node j)).1)) :
    mapTerm decode (UniversalRowLoop.term t (positions s) i.val) =
      mapTerm decodeC (termData ops cache s d i) := by
  simp only [UniversalRowLoop.term, UniversalRowTermProgram.term, mapTerm, termData,
    List.map_map]
  rw [hvalue, hinverse,
    map_factors_eq ops cache t decode decodeC s i hdifference hnegative]
  rfl

theorem map_row_eq (decode : List Bool → A) (decodeC : C → A)
    {V G : Type*} [Fintype V] [DecidableEq V] [DecidableEq G]
    (v : V) (head : V → Fin Q → G) (σ : Fin Q → G) (R : ℕ)
    (d : V → Fin Q → C) (y : V) (delta limit : List Bool)
    (hvalue : ∀ i : Fin Q, decode (t.values.getD i.val []) = decodeC (d y i))
    (hinverse : ∀ i : Fin Q, decode (t.inverses.getD i.val []) = decodeC (cache.inverse i))
    (hdifference : ∀ i j : Fin Q,
      decode ((t.differences.getD i.val []).getD j.val []) = decodeC (cache.difference i j))
    (hnegative : ∀ j : Fin Q, decode (t.negatives.getD j.val []) =
      decodeC ((ops.negRun (cache.node j)).1))
    (hdelta : decode delta = decodeC (if v = y then ops.oneRun.1 else ops.zeroRun.1))
    (hlimit : limit.length = R) :
    mapRow decode
      (UniversalRowDataProgram.row t (positions (mismatchPositions head σ y)) delta limit) =
      mapRow decodeC (rowData ops cache v head σ R d y) := by
  simp only [UniversalRowDataProgram.row, mapRow, rowData, positions_length, hlimit, hdelta]
  by_cases h : (mismatchPositions head σ y).card ≤ R
  · have hy : y ∈ correctionColumns head σ R := (mem_correctionColumns head σ R y).mpr h
    simp only [ite_eq_left h, ite_eq_left hy, positions, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro i _
    exact map_term_eq ops cache t decode decodeC _ (d y) i (hvalue i) (hinverse i)
      (hdifference i) hnegative
  · have hy : y ∉ correctionColumns head σ R := by
      simpa only [mem_correctionColumns] using h
    simp [h, hy]

/-- A scalar-by-scalar decoder refinement suffices for the full polynomial.
The concrete input words need not equal a separately generated canonical
representative of the same field element. -/
theorem row_eval_of_decode [CommRing E] (source : RepresentedRing C E)
    {node : Fin Q → E} (units : NodeUnits node)
    (hnode : ∀ i, source.decode (cache.node i) = node i)
    (hinv : ∀ i, source.decode (cache.inverse i) = units.nodeInverse i)
    (hdiff : ∀ i j, source.decode (cache.difference i j) = units.differenceInverse i j)
    (decode : List Bool → E)
    {V G : Type*} [Fintype V] [DecidableEq V] [DecidableEq G]
    (v : V) (head : V → Fin Q → G) (σ : Fin Q → G) (R : ℕ)
    (d : V → Fin Q → C) (y : V) (delta limit : List Bool)
    (hvalue : ∀ i : Fin Q, decode (t.values.getD i.val []) = source.decode (d y i))
    (hinverse : ∀ i : Fin Q,
      decode (t.inverses.getD i.val []) = source.decode (cache.inverse i))
    (hdifference : ∀ i j : Fin Q,
      decode ((t.differences.getD i.val []).getD j.val []) =
        source.decode (cache.difference i j))
    (hnegative : ∀ j : Fin Q, decode (t.negatives.getD j.val []) =
      source.decode ((source.negRun (cache.node j)).1))
    (hdelta : decode delta =
      source.decode (if v = y then source.oneRun.1 else source.zeroRun.1))
    (hlimit : limit.length = R) :
    (rowExpression Polynomial.X (mapRow (fun bits => Polynomial.C (decode bits))
      (UniversalRowDataProgram.row t (positions (mismatchPositions head σ y)) delta limit))).eval =
      (SubexpTaylorExecution.mapCode source.decode
        (SubexpRepresentedRows.row source.program cache v head σ R d y)).denote := by
  have hr := map_row_eq source.program cache t decode source.decode v head σ R d y
    delta limit hvalue hinverse hdifference hnegative hdelta hlimit
  have hc := congrArg (mapRow (Polynomial.C : E → Polynomial E)) hr
  simp only [mapRow_comp, Function.comp_def] at hc
  rw [hc]
  exact rowData_eval source cache units hnode hinv hdiff v head σ R d y

end SubexponentialSAT.Subexp.UniversalRowTableSource

end OAI.Algorithms
