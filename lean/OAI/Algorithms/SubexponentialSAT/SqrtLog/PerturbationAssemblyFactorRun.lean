import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyFactorBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyInputFrame

namespace OAI.Algorithms

/-! A single polynomial bound for the whole native selected-factor scan. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT BitProgram StructuredCalls DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- The extra factor of n is the deliberately loose uniform bound for each
iteration; every represented dimension still occurs polynomially. -/
def factorWorkPolynomial (n N J t d E H Ksource : ℕ) : ℕ :=
  7*n+n*(n*literalWorkPolynomial n N J t d E H Ksource+2)+
    6*(n*(2*n+2*incidenceBitsBound n J (d*baseWidth 3 t)+4))+15

theorem nativeFactor_polynomial (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : Coeff (baseWidth 3 t) d)
    (rows : FactorRows t N (d:=d)) (s : OuterStore)
    (source : OuterCode) (n Ksource : ℕ)
    (hcount : s 552=List.replicate n true)
    (hrows : ∀ j,j < n → (rows j).length=n)
    (h460 : s 460=[]) (h545 : s 545=[]) (h555 : s 555=[]) (h557 : s 557=[])
    (h561 : s 561=[]) (h569 : s 569=[]) (h573 : s 573=[]) (h585 : s 585=[])
    (hhigh : (s 575).length=n)
    (he : ∀ i∈entryScratch,s (innerPort i)=[])
    (hsource : ∀ j,j < n → ∀ acc, ExecutesOuter source Ksource
      (Function.update (literalReady s (List.replicate j true) acc) 555 (Encoding.encodeNat j))
      (literalSourceState (literalReady s (List.replicate j true) acc) j (sourceWords (rows j))))
    (hinput : ∀ j,j < n → ∀ acc, LowInput t a M cache J N theta (rows j)
      (projectInner (literalSourceState (literalReady s (List.replicate j true) acc)
        j (sourceWords (rows j))))) :
    ExecutesOuter (prepareFactor source)
      (factorWorkPolynomial n N J t d
        ((s 532).length+(s 533).length+(s 583).length) (s 574).length Ksource) s
      (Function.update s 561 (Squarefree.Program.lookupRecords
        (HashCircuitProgram.incidenceEntries
          (fun (_ : Unit) (v : Fin n)=>factorPayload t a M cache J N theta rows s v.val) ()))) := by
  have baseInput : ∀ j,j < n → LowInput t a M cache J N theta (rows j)
      (projectInner (literalSourceState s j (sourceWords (rows j)))) := by
    intro j hj
    apply (hinput j hj []).frame
    intro i h215 h216 h229 h233 h234 h235
    have hn : innerPort i≠569 ∧ innerPort i≠573 := by
      constructor
      · intro he
        apply h229
        have hv := congrArg Fin.val he
        apply Fin.ext
        simp [innerPort] at hv
        omega
      · intro he
        apply h233
        have hv := congrArg Fin.val he
        apply Fin.ext
        simp [innerPort] at hv
        omega
    simp [projectInner,literalSourceState,literalReady,
      Function.update_apply,hn.1,hn.2]
  have hb := factorBodyBudget_bound t a M cache J N theta rows s n Ksource hrows baseInput
  have hp : ∀ j,j < n → (factorPayload t a M cache J N theta rows s j).length ≤
      incidenceBitsBound n J (d*baseWidth 3 t) := by
    intro j hj
    have hz : (s 547).length=d*baseWidth 3 t := by
      simpa [literalSourceState,projectInner,Function.comp_def,innerPort] using
        congrArg List.length (baseInput j hj).zeroWord
    have ho : (s 548).length=d*baseWidth 3 t := by
      simpa [literalSourceState,projectInner,Function.comp_def,innerPort] using
        congrArg List.length (baseInput j hj).oneWord
    simpa [factorPayload,hrows j hj] using
      nativeLiteralValue_length t a M cache J N theta (rows j) s j hz ho
  have ht := tableResult_length_bound (factorPayload t a M cache J N theta rows s)
    (incidenceBitsBound n J (d*baseWidth 3 t)) n hp []
  have hn := nativeFactor_run t a M cache J N theta rows s source n Ksource hcount hrows
    h460 h545 h555 h557 h561 h569 h573 h585 hhigh he hsource hinput
  apply hn.mono
  have hb' := Nat.mul_le_mul_left n (Nat.add_le_add_right hb 2)
  have ht' := Nat.mul_le_mul_left 6 ht
  simp only [List.length_nil,zero_add] at ht'
  unfold factorWorkPolynomial
  omega

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
