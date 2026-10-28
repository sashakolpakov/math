import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblySourceStored
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramIncidence

namespace OAI.Algorithms

/-! Choose typed dictionaries from the actual returned payload bytes. The
same dictionaries carry the source-row meaning and feed the native hash
interpreter; no new serialization or canonical-byte assumption is used. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT SubexpLiftRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open PerturbationAssembly DensePolynomialProgram
open LeafProgram.NativeSemantics

 theorem dictionaryBits_eq_bytes {n B d : ℕ}
    (entries : List (MomentsProgram.Product.Entry n B d)) :
    PerturbationProgram.dictionaryBits entries=MomentsProgram.Product.bytes entries := by
  induction entries with
  | nil => rfl
  | cons e es ih =>
    simp [PerturbationProgram.dictionaryBits,MomentsProgram.Product.bytes,
      MomentsProgram.Normalize.bytes,Squarefree.Program.encodeDictionary,
      Squarefree.Program.rawEntries] at ih ⊢
    exact ih

 theorem payload_family {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J n f : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 p.t) d) (s : OuterStore) (payload : ℕ → List Bool)
    (hc : (s 546).length=n)
    (hz : s 547=RingProgram.flat (RingProgram.modelProgram p.t p.model p.modulus p.cache).zeroRun.1)
    (ho : s 548=RingProgram.flat (RingProgram.modelProgram p.t p.model p.modulus p.cache).oneRun.1)
    (hr : ∀ v : Fin n,payloadRelation p.t p.model p.modulus p.cache J (p.R+1) theta n
      (sourceRowProperty p ps P n f) s v.val (payload v.val)) :
    ∃ incidence : Fin n → List (MomentsProgram.Product.Entry n (baseWidth 3 p.t) d),
      (∀ v,payload v.val=MomentsProgram.Product.bytes (incidence v)) ∧
      (∀ v,Good Finset.univ u J (incidence v)) ∧
      (∀ v,rawDenote p.ops.decode (incidence v)=Squarefree.canonical u J
        (sourceIncidenceJet p ps P n f v.val theta s)) ∧
      (∀ v,(HashCircuitProgram.incidenceEntries
        (fun (_ : Unit) (w : Fin n)=>payload w.val) ()).lookup (Encoding.encodeNat v.val)=
          some (MomentsProgram.Product.bytes (incidence v))) := by
  classical
  have he (v : Fin n) := sourcePayload_realizes p ps P u J n f v.val hu hJ theta s (payload v.val)
    hc hz ho (hr v)
  choose incidence hbytes hgood hden using he
  refine ⟨incidence,?_,hgood,hden,?_⟩
  · intro v
    exact (hbytes v).trans (dictionaryBits_eq_bytes _)
  · intro v
    rw [HashCircuitProgram.incidenceEntries_lookup,(hbytes v).trans (dictionaryBits_eq_bytes _)]

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
