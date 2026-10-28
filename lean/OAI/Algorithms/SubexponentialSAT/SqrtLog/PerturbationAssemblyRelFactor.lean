import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyRelNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyRelOuter

namespace OAI.Algorithms

/-! The actual source witness of each iteration is carried into the final
lookup table, with a uniform polynomial bound on work and table capacity. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def relFactorWorkPolynomial (n N J t d E H Ksource : ℕ) : ℕ :=
  7*n+n*(literalWorkPolynomial n N J t d E H Ksource+2)+
    6*n*literalRecordBound n (incidenceBitsBound n J (d*baseWidth 3 t))+15

theorem nativeFactor_rel (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : Coeff (baseWidth 3 t) d) (n : ℕ)
    (Rows : ℕ → List (Fixed.Array (baseWidth 3 t) d N) → Prop)
    (s : OuterStore) (source : OuterCode) (Ksource : ℕ)
    (h : StagedInput t a M cache J N theta s n)
    (h460 : s 460=[]) (h545 : s 545=[]) (h555 : s 555=[]) (h557 : s 557=[])
    (h561 : s 561=[]) (h569 : s 569=[]) (h573 : s 573=[]) (h585 : s 585=[])
    (hm : (s 575).length=n)
    (hsource : ∀ j,j < n → ∀ acc,
      acc.length ≤ n*literalRecordBound n (incidenceBitsBound n J (d*baseWidth 3 t)) →
      (s 574).getD j false=false → ∀ regs : Fin 16 → Bool,
      ∃ xs k rf,xs.length=n ∧ Rows j xs ∧ k ≤ Ksource ∧
      Eval source k
        (⟨regs,Function.update (literalReady s (List.replicate j true) acc)
          555 (Encoding.encodeNat j)⟩ : OuterData)
        (⟨rf,literalSourceState (literalReady s (List.replicate j true) acc)
          j (Encoding.encodeList Fixed.encode xs)⟩ : OuterData))
    (regs : Fin 16 → Bool) :
    ∃ (payload : ℕ → List Bool) (k : ℕ) (rf : Fin 16 → Bool),
      (∀ j,j < n → (payload j).length ≤ incidenceBitsBound n J (d*baseWidth 3 t) ∧
        payloadRelation t a M cache J N theta n Rows s j (payload j)) ∧
      k ≤ relFactorWorkPolynomial n N J t d
        ((s 532).length+(s 533).length+(s 583).length) (s 574).length Ksource ∧
      Eval (prepareFactor source) k (⟨regs,s⟩ : OuterData)
        (⟨rf,Function.update s 561 (Squarefree.Program.lookupRecords
          (HashCircuitProgram.incidenceEntries
            (fun (_ : Unit) (v : Fin n)=>payload v.val) ()))⟩ : OuterData) := by
  apply prepareFactor_rel_lookup s source (payloadRelation t a M cache J N theta n Rows s)
    (literalWorkPolynomial n N J t d
      ((s 532).length+(s 533).length+(s 583).length) (s 574).length Ksource)
    n (incidenceBitsBound n J (d*baseWidth 3 t)) h.ambientCount
    h460 h573 h569 h561 h585 ?_ regs
  intro j hj acc hacc r
  exact nativeLiteral_rel t a M cache J N theta n Rows s source j Ksource acc h hj
    h545 h555 h557 hm (hsource j hj acc hacc) r

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
