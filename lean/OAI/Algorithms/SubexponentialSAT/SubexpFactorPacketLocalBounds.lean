import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPacketStage
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPrefixCost
import OAI.Algorithms.SubexponentialSAT.Subexp.LagrangePacketBounds

namespace OAI.Algorithms

/-! Numerical bounds for the actual packet row and cache-selection routines. -/

namespace SubexponentialSAT.SubexpFactorPacketBounds

open Subexp.FactorPacketCoordinates (Word Prefix originBytes taylorBytes prefixBytes cacheBytes)
open Subexp.FactorPacketRows (RawRow prefixStream rawRowBytes pairs blueprintRow Valid)

theorem sum_map_le {α : Type*} (xs : List α) (f : α → ℕ) (B : ℕ)
    (h : ∀ x ∈ xs, f x ≤ B) : (xs.map f).sum ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith only [hx, ht]

theorem encoded_le {α : Type*} (enc : α → Word) (xs : List α) (B : ℕ)
    (h : ∀ x ∈ xs, (enc x).length ≤ B) :
    (Encoding.encodeList enc xs).length ≤ (2 * B + 2) * xs.length + 1 := by
  have hs := sum_map_le xs (fun x => (enc x).length) B h
  rw [SubexpFactorPrefixProgram.encoded_length]
  nlinarith only [hs]

theorem length_le_encoded {α : Type*} (enc : α → Word) (xs : List α) :
    xs.length ≤ (Encoding.encodeList enc xs).length := by
  rw [SubexpFactorPrefixProgram.encoded_length]
  omega

theorem member_length_le_encoded {α : Type*} (enc : α → Word) (xs : List α)
    (x : α) (hx : x ∈ xs) : (enc x).length ≤ (Encoding.encodeList enc xs).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    simp only [Encoding.length_encodeList_cons]
    rcases hx with rfl | hx
    · omega
    · have h := ih hx
      omega

def PrefixBound (B : ℕ) (ps : List Prefix) : Prop :=
  ps.length ≤ B ∧ ∀ p ∈ ps, (originBytes p).length ≤ B ∧ (taylorBytes p).length ≤ B

def RowBound (B : ℕ) (row : RawRow) : Prop :=
  row.value.length ≤ B ∧ row.labels.length ≤ B ∧ ∀ w ∈ row.labels, w.length ≤ B

theorem prefixBytes_le {B : ℕ} (hB : 1 ≤ B) (p : Prefix)
    (ho : (originBytes p).length ≤ B) (ht : (taylorBytes p).length ≤ B) :
    (prefixBytes p).length ≤ 6 * B := by
  simp only [prefixBytes, Subexp.LagrangePacketProgram.incidenceFields_length]
  omega

theorem prefixStream_le {B : ℕ} (hB : 1 ≤ B) (ps : List Prefix) (hp : PrefixBound B ps) :
    (prefixStream ps).length ≤ 15 * B^2 := by
  have h := encoded_le prefixBytes ps (6 * B)
    (fun p hmem => prefixBytes_le hB p (hp.2 p hmem).1 (hp.2 p hmem).2)
  change (prefixStream ps).length ≤ _ at h
  have hh := Nat.mul_le_mul_left (2 * (6 * B) + 2) hp.1
  nlinarith only [h, hh, hB]

theorem groupBytes_le {B : ℕ} (hB : 1 ≤ B) (ps : List Prefix) (hp : PrefixBound B ps) :
    (SubexpFactorPrefixProgram.groupBytes ps).length ≤ 34 * B^2 := by
  have hs := prefixStream_le hB ps hp
  have hl := hp.1
  simp only [SubexpFactorPrefixProgram.groupBytes, List.length_append,
    Encoding.length_frame, List.length_replicate]
  nlinarith only [hs, hl, hB]

theorem cache_member_le (cache : List (List Word)) (n : ℕ) (hn : n < cache.length) :
    (Encoding.encodeList id (cache.getD n [])).length ≤ (cacheBytes cache).length := by
  rw [List.getD_eq_getElem cache [] hn]
  simpa only [cacheBytes, ProgramEncoding.encodeRecords,
    SubexpFactorPrefixProgram.encodeList_map, Function.comp_def, id_eq] using
    member_length_le_encoded (Encoding.encodeList id) cache _ (List.getElem_mem hn)

private theorem cache_split (cache : List (List Word)) (n : ℕ) (hn : n < cache.length) :
    cache.take n ++ cache.getD n [] :: cache.drop (n + 1) = cache := by
  rw [List.getD_eq_getElem cache [] hn]
  rw [List.getElem_cons_drop, List.take_append_drop]

theorem selectionCost_le {B : ℕ} (hB : 1 ≤ B) (cache : List (List Word))
    (hc : (cacheBytes cache).length ≤ B) (w : Word) (p : Prefix)
    (hw : w.length ≤ B) (hv : CounterPrograms.value w < cache.length)
    (ho : (originBytes p).length ≤ B) (ht : (taylorBytes p).length ≤ B) :
    Subexp.FactorPacketCoordinates.selectionCost cache (w, p) ≤ 400 * B^2 := by
  have hi : CounterPrograms.value w =
      ((cache.take (CounterPrograms.value w)).map (Encoding.encodeList id)).length := by
    simp [List.length_take, Nat.min_eq_left hv.le]
  have hs := Subexp.LagrangePacketBinary.cost_polynomial
    ((cache.take (CounterPrograms.value w)).map (Encoding.encodeList id))
    (Encoding.encodeList id (cache.getD (CounterPrograms.value w) []))
    ((cache.drop (CounterPrograms.value w + 1)).map (Encoding.encodeList id))
    (prefixBytes p) w hi
  have he : (cache.take (CounterPrograms.value w)).map (Encoding.encodeList id) ++
      Encoding.encodeList id (cache.getD (CounterPrograms.value w) []) ::
        (cache.drop (CounterPrograms.value w + 1)).map (Encoding.encodeList id) =
      cache.map (Encoding.encodeList id) := by
    simpa only [List.map_append, List.map_cons] using
      congrArg (List.map (Encoding.encodeList id)) (cache_split cache _ hv)
  rw [he] at hs
  change Subexp.FactorPacketCoordinates.selectionCost cache (w, p) ≤
    32 * ((cacheBytes cache).length + 1) * (w.length + 1) +
      50 * (cacheBytes cache).length + 21 * (prefixBytes p).length + 61 at hs
  have hp := prefixBytes_le hB p ho ht
  calc
    _ ≤ 32 * ((cacheBytes cache).length + 1) * (w.length + 1) +
      50 * (cacheBytes cache).length + 21 * (prefixBytes p).length + 61 := hs
    _ ≤ 32 * (B + 1) * (B + 1) + 50 * B + 21 * (6 * B) + 61 := by gcongr
    _ ≤ 400 * B^2 := by nlinarith only [hB]

theorem coordinate_le {B : ℕ} (hB : 1 ≤ B) (cache : List (List Word))
    (hc : (cacheBytes cache).length ≤ B) (w : Word) (p : Prefix)
    (hv : CounterPrograms.value w < cache.length)
    (ho : (originBytes p).length ≤ B) (ht : (taylorBytes p).length ≤ B) :
    (Subexp.FactorBlueprint.encodeCoordinate
      (Subexp.FactorPacketCoordinates.coordinate cache (w, p))).length ≤ 16 * B := by
  have hs := (cache_member_le cache _ hv).trans hc
  rw [Subexp.FactorBlueprint.encodeCoordinate_length]
  change 4 * (originBytes p).length + 4 * (taylorBytes p).length +
    2 * (Encoding.encodeList id (cache.getD (CounterPrograms.value w) [])).length + 6 ≤ _
  omega

theorem pairCost_le {B : ℕ} (hB : 1 ≤ B) (cache : List (List Word))
    (hc : (cacheBytes cache).length ≤ B) (w : Word) (p : Prefix)
    (hw : w.length ≤ B) (hv : CounterPrograms.value w < cache.length)
    (ho : (originBytes p).length ≤ B) (ht : (taylorBytes p).length ≤ B) :
    Subexp.FactorPacketCoordinates.pairCost cache (w, p) ≤ 500 * B^2 := by
  have hs := selectionCost_le hB cache hc w p hw hv ho ht
  have hp := prefixBytes_le hB p ho ht
  unfold Subexp.FactorPacketCoordinates.pairCost
  dsimp only [Prod.fst, Prod.snd]
  nlinarith only [hs, hp, hw, hB]

theorem coordinateBudget_le {B : ℕ} (hB : 1 ≤ B) (cache : List (List Word))
    (hc : (cacheBytes cache).length ≤ B) (ps : List Prefix) (hp : PrefixBound B ps)
    (row : RawRow) (hr : RowBound B row) (hv : Valid cache ps row) :
    Subexp.FactorPacketCoordinates.budget cache (pairs ps row) ≤ 1000 * B^3 := by
  have hlen : (pairs ps row).length ≤ B := by
    simpa only [pairs, List.length_zip] using (Nat.min_le_left row.labels.length ps.length).trans hr.2.1
  have hpair : ∀ pair ∈ pairs ps row,
      Subexp.FactorPacketCoordinates.pairCost cache pair ≤ 500 * B^2 := by
    intro pair hm
    have hm' := List.of_mem_zip hm
    exact pairCost_le hB cache hc pair.1 pair.2 (hr.2.2 _ hm'.1)
      (hv.2 _ hm'.1) (hp.2 _ hm'.2).1 (hp.2 _ hm'.2).2
  have hb : ∀ qs : List (Word × Prefix),
      (∀ pair ∈ qs, Subexp.FactorPacketCoordinates.pairCost cache pair ≤ 500 * B^2) →
      Subexp.FactorPacketCoordinates.budget cache qs ≤ qs.length * (500 * B^2 + 3) := by
    intro qs h
    induction qs with
    | nil => simp [Subexp.FactorPacketCoordinates.budget]
    | cons q qs ih =>
      have hh := h q (by simp)
      have ht := ih (fun q hq => h q (by simp [hq]))
      simp only [Subexp.FactorPacketCoordinates.budget, List.length_cons]
      nlinarith only [hh, ht]
  have hh := (hb _ hpair).trans (Nat.mul_le_mul_right _ hlen)
  nlinarith only [hh, hB]

theorem coordinatesBytes_le {B : ℕ} (hB : 1 ≤ B) (cache : List (List Word))
    (hc : (cacheBytes cache).length ≤ B) (ps : List Prefix) (hp : PrefixBound B ps)
    (row : RawRow) (hr : RowBound B row) (hv : Valid cache ps row) :
    (Encoding.encodeList Subexp.FactorBlueprint.encodeCoordinate
      ((pairs ps row).map (Subexp.FactorPacketCoordinates.coordinate cache))).length ≤ 35 * B^2 := by
  have h := encoded_le Subexp.FactorBlueprint.encodeCoordinate
    ((pairs ps row).map (Subexp.FactorPacketCoordinates.coordinate cache)) (16 * B) (by
      intro c hm
      obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hm
      have hm' := List.of_mem_zip hpair
      exact coordinate_le hB cache hc pair.1 pair.2 (hv.2 _ hm'.1)
        (hp.2 _ hm'.2).1 (hp.2 _ hm'.2).2)
  have hl : ((pairs ps row).map (Subexp.FactorPacketCoordinates.coordinate cache)).length ≤ B := by
    simpa only [List.length_map, pairs, List.length_zip] using
      (Nat.min_le_left row.labels.length ps.length).trans hr.2.1
  have hh := h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hl) 1)
  nlinarith only [hh, hB]

theorem rawRowBytes_le {B : ℕ} (hB : 1 ≤ B) (row : RawRow) (hr : RowBound B row) :
    (rawRowBytes row).length ≤ 8 * B^2 := by
  have he := encoded_le id row.labels B hr.2.2
  have hh := he.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hr.2.1) 1)
  have hv := hr.1
  simp only [rawRowBytes, List.length_append, Encoding.length_frame]
  nlinarith only [hh, hv, hB]

theorem blueprintRowBytes_le {B : ℕ} (hB : 1 ≤ B) (cache : List (List Word))
    (hc : (cacheBytes cache).length ≤ B) (ps : List Prefix) (hp : PrefixBound B ps)
    (row : RawRow) (hr : RowBound B row) (hv : Valid cache ps row) :
    (Subexp.FactorBlueprint.encodeRow (blueprintRow cache ps row)).length ≤ 40 * B^2 := by
  have he := coordinatesBytes_le hB cache hc ps hp row hr hv
  have hval := hr.1
  simp only [Subexp.FactorBlueprint.encodeRow, blueprintRow, List.length_append,
    Encoding.length_frame]
  nlinarith only [he, hval, hB]

theorem packetRowCost_le {B : ℕ} (hB : 1 ≤ B) (cache : List (List Word))
    (hc : (cacheBytes cache).length ≤ B) (ps : List Prefix) (hp : PrefixBound B ps)
    (row : RawRow) (hr : RowBound B row) (hv : Valid cache ps row) :
    Subexp.FactorPacketRows.rowCost cache ps row ≤ 3000 * B^3 := by
  have hraw := rawRowBytes_le hB row hr
  have hpre := prefixStream_le hB ps hp
  have hbudget := coordinateBudget_le hB cache hc ps hp row hr hv
  have hcoord := coordinatesBytes_le hB cache hc ps hp row hr hv
  have hout := blueprintRowBytes_le hB cache hc ps hp row hr hv
  have hval := hr.1
  have h12 : B ≤ B^2 := Nat.le_self_pow (by decide) B
  have h23 : B^2 ≤ B^3 := Nat.pow_le_pow_right hB (by decide)
  unfold Subexp.FactorPacketRows.rowCost
  rw [SubexpFactorPrefixProgram.encoded_reverse_length]
  omega

theorem factorBytes_le {B : ℕ} (hB : 1 ≤ B) (cache : List (List Word))
    (hc : (cacheBytes cache).length ≤ B) (ps : List Prefix) (hp : PrefixBound B ps)
    (rows : List RawRow) (hlen : rows.length ≤ B)
    (hr : ∀ row ∈ rows, RowBound B row) (hv : ∀ row ∈ rows, Valid cache ps row) :
    (Subexp.FactorBlueprint.encodeRows (rows.map (blueprintRow cache ps))).length ≤ 100 * B^3 := by
  have he := encoded_le Subexp.FactorBlueprint.encodeRow (rows.map (blueprintRow cache ps))
    (40 * B^2) (by
      intro row hm
      obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hm
      exact blueprintRowBytes_le hB cache hc ps hp row (hr _ hrow) (hv _ hrow))
  simp only [List.length_map] at he
  have hh := he.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hlen) 1)
  change (Subexp.FactorBlueprint.encodeRows _).length ≤ _ at hh
  nlinarith only [hh, hB]

theorem packetRowsRuntime_le {B : ℕ} (hB : 1 ≤ B) (cache : List (List Word))
    (hc : (cacheBytes cache).length ≤ B) (ps : List Prefix) (hp : PrefixBound B ps)
    (rows : List RawRow) (hlen : rows.length ≤ B)
    (hr : ∀ row ∈ rows, RowBound B row) (hv : ∀ row ∈ rows, Valid cache ps row) :
    Subexp.FactorPacketRows.runtimeBound cache ps rows ≤ 5000 * B^4 := by
  have hb : Subexp.FactorPacketRows.rowsBudget cache ps rows ≤ rows.length * (3000 * B^3 + 2) := by
    induction rows with
    | nil => simp [Subexp.FactorPacketRows.rowsBudget]
    | cons row rows ih =>
      have hh := packetRowCost_le hB cache hc ps hp row (hr _ (by simp)) (hv _ (by simp))
      have ht := ih (by simp only [List.length_cons] at hlen; omega)
        (fun x hx => hr x (by simp [hx])) (fun x hx => hv x (by simp [hx]))
      simp only [Subexp.FactorPacketRows.rowsBudget, List.length_cons]
      nlinarith only [hh, ht]
  have hs := hb.trans (Nat.mul_le_mul_right _ hlen)
  have hout := factorBytes_le hB cache hc ps hp rows hlen hr hv
  have h13 : B ≤ B^3 := Nat.le_self_pow (by decide) B
  have h34 : B^3 ≤ B^4 := Nat.pow_le_pow_right hB (by decide)
  unfold Subexp.FactorPacketRows.runtimeBound
  rw [show Subexp.FactorBlueprint.encodeRows ((rows.map (blueprintRow cache ps)).reverse) =
      Encoding.encodeList Subexp.FactorBlueprint.encodeRow ((rows.map (blueprintRow cache ps)).reverse) from rfl,
    SubexpFactorPrefixProgram.encoded_reverse_length]
  change _ ≤ _
  change (Encoding.encodeList Subexp.FactorBlueprint.encodeRow _).length ≤ _ at hout
  nlinarith only [hs, hout, hB, h13, h34]

end SubexponentialSAT.SubexpFactorPacketBounds

end OAI.Algorithms
