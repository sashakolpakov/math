import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOriginControl
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorCacheMap

namespace OAI.Algorithms

/-! Typed formats, lengths, and visit folds for the actual origin map. -/

namespace SubexponentialSAT.SubexpOriginMap

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SubexpOriginControl
open SubexpTaylorCacheCalls (recordStream encodeList_recordStream)

theorem visits_packed {C : Type*} (encode output : C → List Bool) (port : Fin 32)
    (effect : List Bool → Data → Data → Prop)
    (heffect : ∀ bits a b, effect bits a b → ∀ x, encode x = bits →
      b.stacks port = (SubexpTaylorFrames.recordBytes (output x)).reverse ++ a.stacks port)
    (items : List C) (a b : Data)
    (hv : RecordPrograms.Visits (fun _ => false) effect (items.map encode) a b) :
    b.stacks port = (recordStream (items.map output)).reverse ++ a.stacks port := by
  induction items generalizing a with
  | nil => cases hv; simp [recordStream]
  | cons x xs ih =>
      cases hv with
      | hit h _ => cases h
      | @miss _ _ _ middle _ _ he hr =>
          rw [ih middle hr, heffect _ _ _ he x rfl]
          simp [recordStream, List.append_assoc]

theorem visits_unchanged {A : Type*} (measure : Data → A)
    (effect : List Bool → Data → Data → Prop)
    (heffect : ∀ bits a b, effect bits a b → measure b = measure a)
    (items : List (List Bool)) (a b : Data)
    (hv : RecordPrograms.Visits (fun _ => false) effect items a b) :
    measure b = measure a := by
  induction hv with
  | nil => rfl
  | hit h _ => cases h
  | @miss _ _ _ middle _ _ he hr ih => exact ih.trans (heffect _ _ _ he)

theorem encode_injective {B : ℕ} (hB : 0 < B) :
    Function.Injective (SubexpFlatLift.encode (B := B)) := by
  intro a b hab
  apply SubexpNodeLiftData.encode_injective hB
  simpa [SubexpNodeLiftData.encode, SubexpFlatLift.encode, SubexpFlatLift.quadWords,
    SubexpFlatLift.flatten, List.append_assoc] using hab

theorem rowBytes_injective {B : ℕ} (hB : 0 < B) :
    Function.Injective (rowBytes (B := B)) := by
  intro a b hab
  have he := Encoding.encodeList_injective (encode_injective hB) hab
  change a.1 :: a.2 = b.1 :: b.2 at he
  exact Prod.ext (List.cons.inj he).1 (List.cons.inj he).2

theorem degreeBytes_length {B : ℕ} (xs : List (Quad (Word B))) :
    (Encoding.encodeList SubexpFlatLift.encode xs).length = (8 * B + 2) * xs.length + 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [Encoding.length_encodeList_cons, SubexpFlatLift.encode_length, ih]
      simp only [List.length_cons]
      ring

def rowBound (B R : ℕ) := (8 * B + 2) * (R + 1) + 1
def tailBound (B R : ℕ) := (8 * B + 2) * R + 1

theorem rowBytes_length_le {B R : ℕ} (row : Row B) (hr : row.2.length ≤ R) :
    (rowBytes row).length ≤ rowBound B R := by
  rw [rowBytes, degreeBytes_length, List.length_cons]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right hr 1)) 1

def coordinateBound (B b m R : ℕ) : ℕ :=
  3 * rowBound B R + 2 * tailBound B R + 36 * B + 56 * b + 33 +
    SubexpOriginQuadProgram.cost B b m

def coordinatesBound (C B b m R : ℕ) : ℕ :=
  3 + C * (6 * rowBound B R + coordinateBound B b m R + 7) +
    (3 * (C * (8 * b + 2)) + 8)

def incidenceInputBound (C B R : ℕ) : ℕ := 1 + (2 * rowBound B R + 2) * C
def incidenceOutputBound (C b : ℕ) : ℕ := 1 + (8 * b + 2) * C
def incidenceBound (C B b m R : ℕ) : ℕ :=
  3 * incidenceInputBound C B R + coordinatesBound C B b m R +
    14 * incidenceOutputBound C b + 22

def iterationsBound (I C B b m R : ℕ) : ℕ :=
  3 + I * (6 * incidenceInputBound C B R + incidenceBound C B b m R + 7)

def tableBound (I C B b m R : ℕ) : ℕ :=
  7 * (1 + (2 * incidenceInputBound C B R + 2) * I) + 5 +
    iterationsBound I C B b m R + (3 * (I * (2 * incidenceOutputBound C b + 2)) + 8) + 1

variable (p : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1)
variable (width : List Bool) (hw : width.length = baseWidth p 1)

def originBytes {B : ℕ} (row : Row B) : List Bool :=
  SubexpFlatLift.encode (SubexpOriginResidue.quad p M width hw row.1)

omit [Fact p.Prime] in
@[simp] theorem originBytes_length {B : ℕ} (row : Row B) :
    (originBytes p M width hw row).length = 4 * baseWidth p 1 :=
  SubexpFlatLift.encode_length _

def incidenceBytes {B : ℕ} (rows : List (Row B)) := Encoding.encodeList rowBytes rows
def incidenceOutput {B : ℕ} (rows : List (Row B)) :=
  Encoding.encodeList (originBytes p M width hw) rows

omit [Fact p.Prime] in
theorem origin_stream_length {B : ℕ} (rows : List (Row B)) :
    (recordStream (rows.map (originBytes p M width hw))).length =
      rows.length * (8 * baseWidth p 1 + 2) := by
  induction rows with
  | nil => simp [recordStream]
  | cons x xs ih =>
      change (SubexpTaylorFrames.recordBytes (originBytes p M width hw x) ++
        recordStream (xs.map (originBytes p M width hw))).length = _
      simp only [List.length_append, SubexpTaylorFrames.recordBytes, List.length_cons,
        Encoding.length_frame, originBytes_length, ih]
      ring

omit [Fact p.Prime] in
theorem incidenceOutput_length {B : ℕ} (rows : List (Row B)) :
    (incidenceOutput p M width hw rows).length = incidenceOutputBound rows.length (baseWidth p 1) := by
  rw [incidenceOutput, ← SubexpTaylorRow.encode_map, encodeList_recordStream,
    List.length_append, origin_stream_length]
  simp only [List.length_singleton, incidenceOutputBound]
  ring

theorem incidenceBytes_length_le {B R : ℕ} (rows : List (Row B))
    (hr : ∀ row ∈ rows, row.2.length ≤ R) :
    (incidenceBytes rows).length ≤ incidenceInputBound rows.length B R :=
  Encoding.length_encodeList_upper rowBytes rows (rowBound B R)
    (fun row hrow => rowBytes_length_le row (hr row hrow))

theorem incidenceBound_mono {C D : ℕ} (h : C ≤ D) (B b m R : ℕ) :
    incidenceBound C B b m R ≤ incidenceBound D B b m R := by
  unfold incidenceBound incidenceInputBound incidenceOutputBound coordinatesBound
  gcongr

theorem outputBytes_length {B : ℕ} (rows : List (List (Row B))) :
    (outputBytes p M width hw rows).length =
      1 + 4 * rows.length + (16 * baseWidth p 1 + 4) * (rows.map List.length).sum := by
  change (Encoding.encodeList (incidenceOutput p M width hw) rows).length = _
  induction rows with
  | nil => simp
  | cons coordinates rest ih =>
      rw [Encoding.length_encodeList_cons, incidenceOutput_length, ih]
      simp only [List.length_cons, List.map_cons, List.sum_cons, incidenceOutputBound]
      ring

end SubexponentialSAT.SubexpOriginMap

end OAI.Algorithms
