import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequenceModule
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.ParameterTorReduction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.PrimeEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.EulerTruncation
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.EulerTransport

/-! # Sequence Reduction -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequenceReduction

noncomputable section

/-! Removing the first element of a native regular sequence gives
the actual tail quotient over the parameter ring, preserving native
Tor Euler pairings whenever that parameter is regular on the other input. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory

universe u

open RingTheory.Sequence

variable (R : Type u) [CommRing R] (r : R)

def quotientEquiv (I : Ideal R) :
    (Parameter.ScalarQuotient.quotient R r).obj (.of R (R ⧸ I)) ≃ₗ[Parameter.ScalarQuotient.Ring R r]
      Parameter.ScalarQuotient.Ring R r ⧸ I.map (Ideal.Quotient.mk (Ideal.span {r})) :=
  (Parameter.ScalarQuotient.baseChangeEquiv R r (.of R (R ⧸ I))).trans
    (Ideal.qoutMapEquivTensorQout (R := R) (I := I) (Parameter.ScalarQuotient.Ring R r)).symm

def tailEquiv (rs : List R) :
    (Parameter.ScalarQuotient.quotient R r).obj (SequenceModule.quotient R (r :: rs)) ≃ₗ[
      Parameter.ScalarQuotient.Ring R r]
    SequenceModule.quotient (Parameter.ScalarQuotient.Ring R r)
      (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) := by
  have hI : (Ideal.ofList (r :: rs)).map (Ideal.Quotient.mk (Ideal.span {r})) =
      Ideal.ofList (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) := by
    have hz : Ideal.Quotient.mk (Ideal.span {r}) r = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (Set.mem_singleton r))
    rw [Ideal.map_ofList, List.map_cons, Ideal.ofList_cons, hz]
    simp
  exact (quotientEquiv R r (Ideal.ofList (r :: rs))).trans (Submodule.quotEquivOfEq _ _ hI)

theorem tail_regular (rs : List R) (hreg : IsRegular R (r :: rs)) :
    IsRegular (Parameter.ScalarQuotient.Ring R r) (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) := by
  let e : QuotSMulTop r R ≃ₗ[Parameter.ScalarQuotient.Ring R r] Parameter.ScalarQuotient.Ring R r :=
    (Parameter.PrimeEuler.quotientEquiv R r).symm.extendScalarsOfSurjective
      (show Function.Surjective (algebraMap R (Parameter.ScalarQuotient.Ring R r)) from Ideal.Quotient.mk_surjective)
  exact (e.isRegular_congr _).mp ((isRegular_cons_iff' R r rs).mp hreg).2

theorem localRing [IsLocalRing R] (rs : List R) (hreg : IsRegular R (r :: rs)) :
    IsLocalRing (Parameter.ScalarQuotient.Ring R r) := by
  let : Nontrivial (Parameter.ScalarQuotient.Ring R r) := (tail_regular R r rs hreg).nontrivial
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {r})) Ideal.Quotient.mk_surjective

theorem euler (rs : List R) (hreg : IsRegular R (r :: rs))
    (N : ModuleCat.{u} R) (hN : IsSMulRegular N r) (d : ℕ) :
    Tor.Euler.euler (Parameter.ScalarQuotient.Ring R r)
      (SequenceModule.quotient (Parameter.ScalarQuotient.Ring R r)
        (rs.map (Ideal.Quotient.mk (Ideal.span {r}))))
      ((Parameter.ScalarQuotient.quotient R r).obj N) d =
    Tor.Euler.euler R (SequenceModule.quotient R (r :: rs)) N d := by
  have h := ParameterTorReduction.euler R r ((isRegular_cons_iff R r rs).mp hreg).1
    (SequenceModule.quotient R (r :: rs)) N
    (SequenceModule.killed R (r :: rs) r (List.mem_cons_self)) hN d
  exact (PrimeFiltrationEuler.euler_iso_left (Parameter.ScalarQuotient.Ring R r)
    (tailEquiv R r rs).toModuleIso ((Parameter.ScalarQuotient.quotient R r).obj N) d).symm.trans h

theorem euler_length [IsNoetherianRing R] [IsLocalRing R]
    (rs : List R) (hreg : IsRegular R (r :: rs))
    (N : ModuleCat.{u} R) (hN : IsSMulRegular N r) :
    Tor.Euler.euler R N (SequenceModule.quotient R (r :: rs)) (r :: rs).length =
      Tor.Euler.euler (Parameter.ScalarQuotient.Ring R r)
        ((Parameter.ScalarQuotient.quotient R r).obj N)
        (SequenceModule.quotient (Parameter.ScalarQuotient.Ring R r)
          (rs.map (Ideal.Quotient.mk (Ideal.span {r})))) rs.length := by
  let := localRing R r rs hreg
  let A := SequenceModule.quotient (Parameter.ScalarQuotient.Ring R r)
    (rs.map (Ideal.Quotient.mk (Ideal.span {r})))
  let : HasProjectiveDimensionLE A rs.length := by
    simpa only [List.length_map] using SequenceModule.projectiveDimension
      (Parameter.ScalarQuotient.Ring R r) (rs.map (Ideal.Quotient.mk (Ideal.span {r})))
      (tail_regular R r rs hreg)
  exact (Tor.EulerTransport.comm R N (SequenceModule.quotient R (r :: rs)) (r :: rs).length).trans
    ((euler R r rs hreg N hN (r :: rs).length).symm.trans
      ((Tor.EulerTransport.comm (Parameter.ScalarQuotient.Ring R r) A
        ((Parameter.ScalarQuotient.quotient R r).obj N) (r :: rs).length).trans
        (Tor.EulerTruncation.stable (Parameter.ScalarQuotient.Ring R r)
          ((Parameter.ScalarQuotient.quotient R r).obj N) A rs.length (r :: rs).length (by simp))))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequenceReduction
