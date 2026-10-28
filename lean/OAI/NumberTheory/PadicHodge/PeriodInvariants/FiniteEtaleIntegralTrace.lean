import OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteProductTrace
import Mathlib.RingTheory.Etale.Field

/-! # Finite Etale Integral Trace -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteEtaleIntegralTrace

noncomputable section

/-! # The canonical trace of a finite étale algebra preserves integral elements -/

universe u v
variable (R : Type v) [CommRing R] (K E : Type u) [Field K] [CommRing E]
  [Algebra R K] [Algebra R E] [Algebra K E] [IsScalarTower R K E]

theorem integral [Algebra.Etale K E] {x : E} (hx : IsIntegral R x) :
    IsIntegral R (Algebra.trace K E x) := by
  obtain ⟨ι, hι, L, hL, hKL, e, hprop⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K E).mp inferInstance
  have := hι
  let : Fintype ι := Fintype.ofFinite ι
  let (i : ι) : Field (L i) := hL i
  let (i : ι) : Algebra K (L i) := hKL i
  let (i : ι) : Algebra R (L i) := ((algebraMap K (L i)).comp (algebraMap R K)).toAlgebra
  have (i : ι) : IsScalarTower R K (L i) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have (i : ι) : FiniteDimensional K (L i) := (hprop i).1
  have hi (i : ι) : IsIntegral R (e x i) :=
    IsIntegral.map (((Pi.evalAlgHom K L i).comp e.toAlgHom).restrictScalars R) hx
  rw [← Algebra.trace_eq_of_algEquiv e x, FiniteProductTrace.of_field K L]
  exact IsIntegral.sum (fun i => Algebra.trace K (L i) (e x i))
    (fun i _ => Algebra.isIntegral_trace (hi i))

def trace [Algebra.Etale K E] : integralClosure R E →ₗ[R] integralClosure R K :=
  (((Algebra.trace K E).restrictScalars R).comp
    (integralClosure R E).toSubmodule.subtype).codRestrict
      (integralClosure R K).toSubmodule (fun x => integral R K E x.property)

theorem trace_coe [Algebra.Etale K E] (x : integralClosure R E) :
    (FiniteEtaleIntegralTrace.trace R K E x).val = Algebra.trace K E x.val := rfl

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteEtaleIntegralTrace
