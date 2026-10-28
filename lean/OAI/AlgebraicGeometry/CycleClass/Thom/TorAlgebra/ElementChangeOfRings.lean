import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.IndependentLength
import OAI.AlgebraicGeometry.CycleClass.Thom.Tor.RegularSequence
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.EulerTransport

/-! # Element Change Of Rings -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ElementChangeOfRings.Regular

noncomputable section

/-! Cutting by an element regular on the ring and on the second
module preserves native Tor lengths after passing to the quotient ring.
The second module becomes its actual quotient by that element. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits RingTheory.Sequence

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FlatExtension OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler.Tor OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.EulerTransport.Tor
open OAI.AlgebraicGeometry.CycleClass.Thom.Tor.RegularSequence.Constructions

set_option backward.isDefEq.respectTransparency false

universe u
variable (R : Type u) [CommRing R] (r : R) (N : ModuleCat.{u} R)

theorem quotient_tor_isZero (hr : IsSMulRegular R r) (hn : IsSMulRegular N r) (n : ℕ) :
    IsZero (((Tor (ModuleCat R) (n + 1)).obj (ModuleCat.of R (R ⧸ Ideal.span {r}))).obj N) := by
  have h := Thom.Tor.RegularSequence.Constructions.higherTor_regular_quotient_isZero R N [r]
    ((isWeaklyRegular_singleton_iff R r).mpr hr) ((isWeaklyRegular_singleton_iff N r).mpr hn) n
  rw [Ideal.ofList_singleton] at h
  exact h

def quotientTensorIso : ModuleCat.of (R ⧸ Ideal.span {r}) (QuotSMulTop r N) ≅
    (FlatExtension.baseChange R (R ⧸ Ideal.span {r})).obj N :=
  ((QuotSMulTop.equivQuotTensor r N).extendScalarsOfSurjective
    (show Function.Surjective (algebraMap R (R ⧸ Ideal.span {r})) from Ideal.Quotient.mk_surjective)).toModuleIso

variable (M : ModuleCat.{u} (R ⧸ Ideal.span {r}))
  (hr : IsSMulRegular R r) (hn : IsSMulRegular N r)

include hr hn

theorem tor_length (n : ℕ) :
    Module.length R (((Tor (ModuleCat R) n).obj
      ((ModuleCat.restrictScalars (algebraMap R (R ⧸ Ideal.span {r}))).obj M)).obj N) =
    Module.length (R ⧸ Ideal.span {r}) (((Tor (ModuleCat (R ⧸ Ideal.span {r})) n).obj M).obj
      (ModuleCat.of (R ⧸ Ideal.span {r}) (QuotSMulTop r N))) :=
  (IndependentLength.Tor.tor_length R (R ⧸ Ideal.span {r}) M N
    Ideal.Quotient.mk_surjective (quotient_tor_isZero R r N hr hn) n).symm.trans
      ((((Tor (ModuleCat (R ⧸ Ideal.span {r})) n).obj M).mapIso (quotientTensorIso R r N).symm).toLinearEquiv.length_eq)

theorem euler_eq (d : ℕ) :
    Euler.Tor.euler R ((ModuleCat.restrictScalars (algebraMap R (R ⧸ Ideal.span {r}))).obj M) N d =
    Euler.Tor.euler (R ⧸ Ideal.span {r}) M (ModuleCat.of (R ⧸ Ideal.span {r}) (QuotSMulTop r N)) d := by
  apply Finset.sum_congr rfl
  intro n _
  exact congrArg (fun l : ℕ∞ => (-1 : ℚ) ^ n * (l.toNat : ℚ)) (tor_length R r N M hr hn n)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ElementChangeOfRings.Regular
