import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequenceModule
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.QuotientFiniteSupport

/-! # Sequence Finite Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequenceFiniteSupport

noncomputable section

/-! A nonempty regular-sequence quotient has zero native Euler
pairing against any finite module supported at one point. The argument
uses the last scalar exact sequence, without a domain hypothesis. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory
open scoped Pointwise

universe u

open RingTheory.Sequence OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequenceModule

variable (R : Type u) [CommRing R]

def modelEquiv (rs : List R) : SequenceModule.quotient R rs ≃ₗ[R] R ⧸ (Ideal.ofList rs • (⊤ : Submodule R R)) :=
  Submodule.quotEquivOfEq _ _ (by rw [smul_eq_mul, Ideal.mul_top])

def outerEquiv (r : R) (rs : List R) : SequenceModule.quotient R (r :: rs) ≃ₗ[R] QuotSMulTop r (SequenceModule.quotient R rs) :=
  (modelEquiv R (r :: rs)).trans
    ((Submodule.quotOfListConsSMulTopEquivQuotSMulTopOuter R r rs).trans
      (QuotSMulTop.congr r (modelEquiv R rs).symm))

theorem regular_last [IsNoetherianRing R] [IsLocalRing R]
    (r : R) (rs : List R) (hreg : IsRegular R (r :: rs)) : IsSMulRegular (SequenceModule.quotient R rs) r := by
  have ht : IsRegular R (rs ++ [r]) := IsLocalRing.isRegular_of_perm hreg
    (by simpa only [List.singleton_append] using (List.perm_append_comm (l₁ := [r]) (l₂ := rs)))
  have hr := ((isWeaklyRegular_append_iff R rs [r]).mp ht.toIsWeaklyRegular).2
  have h := ((isWeaklyRegular_cons_iff _ r []).mp hr).1
  exact ((modelEquiv R rs).isSMulRegular_congr r).mpr h

theorem euler_zero [IsNoetherianRing R] [IsLocalRing R]
    (r : R) (rs : List R) (hreg : IsRegular R (r :: rs))
    (N : ModuleCat.{u} R) [Module.Finite R N] (p : PrimeSpectrum R) (hN : Module.support R N ⊆ {p}) :
    Tor.Euler.euler R N (SequenceModule.quotient R (r :: rs)) (r :: rs).length = 0 := by
  let := SequenceModule.projectiveDimension R (r :: rs) hreg
  let e := outerEquiv R r rs
  let : HasProjectiveDimensionLE (ModuleCat.of R (QuotSMulTop r (SequenceModule.quotient R rs))) (r :: rs).length :=
    hasProjectiveDimensionLT_of_iso e.toModuleIso ((r :: rs).length + 1)
  have hz := QuotientFiniteSupport.euler_zero R (SequenceModule.quotient R rs) N r
    (regular_last R r rs hreg) (r :: rs).length p hN
  exact (Tor.EulerTransport.comm R N (SequenceModule.quotient R (r :: rs)) (r :: rs).length).trans
    ((PrimeFiltrationEuler.euler_iso_left R e.toModuleIso N (r :: rs).length).trans hz)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequenceFiniteSupport
