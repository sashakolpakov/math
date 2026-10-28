import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblySource
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyRelStored
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramOutput

namespace OAI.Algorithms

/-! The executed source predicate determines the incidence jet independently
of the particular coefficient-array witness returned by each source call. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram LeafProgram.NativeSemantics
open scoped BigOperators

/-- Replacing decoded source rows and selected bits by their fixed meanings
commutes with the harmless equal-dimension transport of the emitted jet. -/
theorem nativeStored_fixed_rows (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u J N n : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)) (hlen : rows.length=n)
    (family : Fin n → Polynomial (a.O t)) (bits : Fin n → Bool)
    (hrow : ∀ i : Fin rows.length,
      PerturbationProgram.polynomial (RingProgram.modelRing t ht hd a M cache) rows[i].1.val =
        family (Fin.cast hlen i))
    (hbits : ∀ i : Fin rows.length, rows[i].2 = bits (Fin.cast hlen i)) :
    castJet hlen (nativeStored t ht hd a M cache u J N hu hJ theta rows).denote =
      Squarefree.canonical u J (Moments.incidenceJet family
        ((RingProgram.modelRing t ht hd a M cache).decode theta)
        (∑ v : Fin n, (family v).eval ((RingProgram.modelRing t ht hd a M cache).decode theta) *
          (if bits v then 1 else 0))) := by
  subst n
  simp only [Fin.cast_refl] at hrow hbits
  change (nativeStored t ht hd a M cache u J N hu hJ theta rows).denote = _
  rw [nativeStored_denote]
  simp_rw [hrow,hbits]
  rfl

noncomputable def fixedSourceRow {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (n f j : ℕ) (v : Fin n) : Polynomial (p.model.O p.t) :=
  sourceRowFamily ps n f j (totalPackedSource p P) v.val

theorem sourceRowProperty_polynomial {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (n f j : ℕ) (xs : List (Fixed.Array (baseWidth 3 p.t) d (p.R+1)))
    (hs : sourceRowProperty p ps P n f j xs) (i : ℕ) (hi : i < xs.length) :
    PerturbationProgram.polynomial p.ops xs[i].val =
      sourceRowFamily ps n f j (totalPackedSource p P) i := by
  have he := (RowProperty.getElem Fixed.encode _ _ 0 xs hs i hi).1
  simpa only [PolynomialExecutorProgram.meaning,PerturbationProgram.polynomial,
    SubexponentialSAT.SubexpDensePolynomial.decodeList,Nat.zero_add] using he

/-- Concrete low-branch semantics from the actual source-call postcondition. -/
theorem sourceRows_nativeStored {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J n f j : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 p.t) d)
    (xs : List (Fixed.Array (baseWidth 3 p.t) d (p.R+1))) (hx : xs.length=n)
    (choice : List Bool) (hc : choice.length=n)
    (hs : sourceRowProperty p ps P n f j xs) :
    castJet ((pairChoice_length xs choice (hx.trans hc.symm)).trans hx)
      (nativeStored p.t p.ht p.hd p.model p.modulus p.cache u J (p.R+1) hu hJ theta
        (pairChoice xs choice)).denote =
      Squarefree.canonical u J (Moments.incidenceJet (fixedSourceRow p ps P n f j)
        (p.ops.decode theta)
        (∑ v : Fin n, (fixedSourceRow p ps P n f j v).eval (p.ops.decode theta) *
          (if choice.getD v.val false then 1 else 0))) := by
  apply nativeStored_fixed_rows p.t p.ht p.hd p.model p.modulus p.cache u J (p.R+1) n
    hu hJ theta (pairChoice xs choice) _ (fixedSourceRow p ps P n f j)
    (fun v => choice.getD v.val false)
  · intro i
    have hi : i.val < xs.length := by
      have := i.isLt
      simp only [pairChoice,List.length_zip] at this
      omega
    have he := sourceRowProperty_polynomial p ps P n f j xs hs i.val hi
    change PerturbationProgram.polynomial p.ops ((xs.zip choice)[i.val]).1.val = _
    rw [List.getElem_zip]
    exact he
  · intro i
    have hi : i.val < choice.length := by
      have := i.isLt
      simp only [pairChoice,List.length_zip] at this
      omega
    change ((xs.zip choice)[i.val]).2 = choice.getD i.val false
    simp only [List.getElem_zip,List.getD_eq_getElem _ _ hi]

/-- Witness-free intended jet: the low branch uses the fixed source family;
the high branch is exactly the current fixed Boolean assignment. -/
noncomputable def sourceIncidenceJet {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (n f j : ℕ) (theta : Coeff (baseWidth 3 p.t) d) (s : OuterStore) :
    Squarefree.Jet (Fin n) (p.model.O p.t) :=
  if (s 574).getD j false then
    Squarefree.Sparse.atom Squarefree.Index.origin (if (s 575).getD j false then 1 else 0)
  else Moments.incidenceJet (fixedSourceRow p ps P n f j) (p.ops.decode theta)
    (∑ v : Fin n, (fixedSourceRow p ps P n f j v).eval (p.ops.decode theta) *
      (if (s 546).getD v.val false then 1 else 0))

theorem sourcePayload_realizes {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J n f j : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 p.t) d) (s : OuterStore) (payload : List Bool)
    (hc : (s 546).length=n)
    (hz : s 547=RingProgram.flat (RingProgram.modelProgram p.t p.model p.modulus p.cache).zeroRun.1)
    (ho : s 548=RingProgram.flat (RingProgram.modelProgram p.t p.model p.modulus p.cache).oneRun.1)
    (hr : payloadRelation p.t p.model p.modulus p.cache J (p.R+1) theta n
      (sourceRowProperty p ps P n f) s j payload) :
    ∃ entries : List (MomentsProgram.Product.Entry n (baseWidth 3 p.t) d),
      payload=PerturbationProgram.dictionaryBits entries ∧ Good Finset.univ u J entries ∧
      rawDenote p.ops.decode entries = Squarefree.canonical u J
        (sourceIncidenceJet p ps P n f j theta s) := by
  obtain ⟨entries,hbytes,hgood,hden⟩ := payloadRelation_realizes p.t p.ht p.hd p.model
    p.modulus p.cache u J (p.R+1) n hu hJ theta (sourceRowProperty p ps P n f)
    s j payload hc hz ho hr
  refine ⟨entries,hbytes,hgood,?_⟩
  cases hh : (s 574).getD j false
  · simp only [hh,Bool.false_eq_true,ite_false] at hden
    obtain ⟨xs,hx,hRows,he⟩ := hden
    change rawDenote p.ops.decode entries = _ at he
    simpa only [sourceIncidenceJet,hh,Bool.false_eq_true,ite_false] using
      he.trans (sourceRows_nativeStored p ps P u J n f j hu hJ theta xs hx (s 546) hc hRows)
  · simp only [hh,ite_true] at hden
    change rawDenote p.ops.decode entries = _ at hden
    simpa only [sourceIncidenceJet,hh,ite_true] using hden

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
