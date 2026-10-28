import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOriginControl

namespace OAI.Algorithms

/-! The physical origin mapper reads exactly the already-computed Taylor
cache. This adapter supplies its nonempty-row representation and identifies
the resulting source-field values without assuming an origin table. -/

namespace SubexponentialSAT.SubexpOriginCacheSemantics

open SubexpLiftRing SubexpQuarticRing SubexpOriginControl

private theorem encode_map {α β : Type*} (enc : β → List Bool) (f : α → β)
    (xs : List α) : Encoding.encodeList enc (xs.map f) =
      Encoding.encodeList (fun x => enc (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, Encoding.encodeList, ih]

theorem encode_eq_flat {B : ℕ} (a : Quad (Word B)) :
    SubexpFlatLift.encode a = SubexpTaylorRow.flat a := by
  simp [SubexpFlatLift.encode, SubexpFlatLift.flatten, SubexpFlatLift.quadWords,
    SubexpTaylorRow.flat, SubexpQuarticFlatMul.flat,
    SubexpQuarticFlatMul.wordLists, FourWordPrograms.flatWords, Quad.toFn]

variable (p μ : ℕ) [Fact p.Prime]
variable (source : SubexpSelectedConversions.Prepared p 0)
variable (target : SubexpPreparedQuartic.Modulus p μ)
variable (reduction theta : SubexpTaylorRow.Code p μ)
variable (R N : ℕ) (hN : 0 < N)

def cacheRow (e : SubexpTaylorRowCorrectness.RowExpr p) : Row (baseWidth p μ) :=
  (SubexpTaylorRowCorrectness.entry p μ source target reduction theta R N e ⟨0, hN⟩,
    (SubexpTaylorRowCorrectness.column p μ source target reduction theta R N e).tail)

theorem cacheRow_cons (e : SubexpTaylorRowCorrectness.RowExpr p) :
    (cacheRow p μ source target reduction theta R N hN e).1 ::
      (cacheRow p μ source target reduction theta R N hN e).2 =
      SubexpTaylorRowCorrectness.column p μ source target reduction theta R N e := by
  have hl := SubexpTaylorRowCorrectness.column_length p μ source target reduction theta R N e
  cases hc : SubexpTaylorRowCorrectness.column p μ source target reduction theta R N e with
  | nil => simp only [hc, List.length_nil] at hl; omega
  | cons x xs => simp only [cacheRow, SubexpTaylorRowCorrectness.entry, hc]; rfl

theorem cacheRow_tail_length (e : SubexpTaylorRowCorrectness.RowExpr p) :
    (cacheRow p μ source target reduction theta R N hN e).2.length = N - 1 := by
  simp only [cacheRow, List.length_tail, SubexpTaylorRowCorrectness.column_length]

theorem rowBytes_cacheRow (e : SubexpTaylorRowCorrectness.RowExpr p) :
    rowBytes (cacheRow p μ source target reduction theta R N hN e) =
      Encoding.encodeList SubexpTaylorRow.flat
        (SubexpTaylorRowCorrectness.column p μ source target reduction theta R N e) := by
  rw [rowBytes, cacheRow_cons]
  have he : @SubexpFlatLift.encode (baseWidth p μ) = SubexpTaylorRow.flat :=
    funext encode_eq_flat
  rw [he]

def cacheRows (es : List (List (SubexpTaylorRowCorrectness.RowExpr p))) :
    List (List (Row (baseWidth p μ))) :=
  es.map (List.map (cacheRow p μ source target reduction theta R N hN))

def taylorBytes (es : List (List (SubexpTaylorRowCorrectness.RowExpr p))) : List Bool :=
  Encoding.encodeList (Encoding.encodeList (fun e =>
    Encoding.encodeList SubexpTaylorRow.flat
      (SubexpTaylorRowCorrectness.column p μ source target reduction theta R N e))) es

theorem inputBytes_cacheRows (es : List (List (SubexpTaylorRowCorrectness.RowExpr p))) :
    inputBytes (cacheRows p μ source target reduction theta R N hN es) =
      taylorBytes p μ source target reduction theta R N es := by
  unfold inputBytes cacheRows taylorBytes
  rw [encode_map]
  apply congrArg (fun enc => Encoding.encodeList enc es)
  funext incidence
  rw [encode_map]
  apply congrArg (fun enc => Encoding.encodeList enc incidence)
  funext e
  exact rowBytes_cacheRow p μ source target reduction theta R N hN e

variable (M : SubexpPreparedQuartic.Modulus p 1)
variable (width : List Bool) (hw : width.length = baseWidth p 1)

def origin (e : SubexpTaylorRowCorrectness.RowExpr p) : Quad (Word (baseWidth p 1)) :=
  SubexpOriginResidue.quad p M width hw
    (SubexpTaylorRowCorrectness.entry p μ source target reduction theta R N e ⟨0, hN⟩)

def origins (es : List (List (SubexpTaylorRowCorrectness.RowExpr p))) :
    List (List (Quad (Word (baseWidth p 1)))) :=
  es.map (List.map (origin p μ source target reduction theta R N hN M width hw))

theorem outputBytes_cacheRows (es : List (List (SubexpTaylorRowCorrectness.RowExpr p))) :
    outputBytes p M width hw (cacheRows p μ source target reduction theta R N hN es) =
      Encoding.encodeList (Encoding.encodeList SubexpFlatLift.encode)
        (origins p μ source target reduction theta R N hN M width hw es) := by
  unfold outputBytes cacheRows origins
  rw [encode_map, encode_map]
  apply congrArg (fun enc => Encoding.encodeList enc es)
  funext incidence
  rw [encode_map, encode_map]
  rfl

theorem origin_decode (hμ : 0 < μ)
    (hreduction : reduction.map (wordValue p μ) =
      reductionData (QuarticSearch.liftedCoefficients p μ))
    (e : SubexpTaylorRowCorrectness.RowExpr p)
    (hdegree : ((e.map (SubexpRowSourceSemantics.denote source)).eval).natDegree ≤ R) :
    source.residueRing.decode (origin p μ source target reduction theta R N hN M width hw e) =
      ((e.map (SubexpRowSourceSemantics.denote source)).eval).eval
        (SubexpActualRing.rho p μ hμ
          (SubexpHornerMachine.decode p μ (QuarticSearch.liftedCoefficients p μ) theta)) :=
  SubexpOriginResidue.shifted_entry_origin p M width hw μ hμ source target reduction theta
    hreduction R N hN e hdegree

end SubexponentialSAT.SubexpOriginCacheSemantics

end OAI.Algorithms
