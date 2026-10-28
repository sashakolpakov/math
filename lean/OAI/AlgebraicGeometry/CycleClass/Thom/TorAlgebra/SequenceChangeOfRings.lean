import OAI.AlgebraicGeometry.CycleClass.Thom.Regular.EquationQuotients
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ElementChangeOfRings
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.IsolatedEuler

/-! # Sequence Change Of Rings -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.SequenceChangeOfRings

noncomputable section

/-! Change of rings for the actual complete-intersection quotient,
with the residual quotient identified by the third isomorphism theorem. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits RingTheory.Sequence

open OAI.AlgebraicGeometry.CycleClass.Thom.Regular.EquationQuotients.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler.Tor

set_option backward.isDefEq.respectTransparency false

universe u
variable (R : Type u) [CommRing R] (r : R) (rs : List R)

theorem sequenceQuotientEquiv_algebraMap_smul (a : R)
    (x : (R ⧸ Ideal.span {r}) ⧸ Ideal.ofList (rs.map (algebraMap R (R ⧸ Ideal.span {r})))) :
    Regular.EquationQuotients.Constructions.sequenceQuotientEquiv R r rs (algebraMap R (R ⧸ Ideal.span {r}) a • x) =
      a • Regular.EquationQuotients.Constructions.sequenceQuotientEquiv R r rs x := by
  rw [algebraMap_smul, map_smul]

def restrictedSequenceQuotientIso :
    (ModuleCat.restrictScalars (algebraMap R (R ⧸ Ideal.span {r}))).obj
      (ModuleCat.of (R ⧸ Ideal.span {r})
        ((R ⧸ Ideal.span {r}) ⧸ Ideal.ofList (rs.map (algebraMap R (R ⧸ Ideal.span {r}))))) ≅
      ModuleCat.of R (R ⧸ Ideal.ofList (r :: rs)) :=
  LinearEquiv.toModuleIso
    { (Regular.EquationQuotients.Constructions.sequenceQuotientEquiv R r rs).toAddEquiv with
      map_smul' := sequenceQuotientEquiv_algebraMap_smul R r rs }

theorem euler_eq (N : ModuleCat.{u} R) (hr : IsSMulRegular R r) (hn : IsSMulRegular N r) (d : ℕ) :
    Euler.Tor.euler R (ModuleCat.of R (R ⧸ Ideal.ofList (r :: rs))) N d =
      Euler.Tor.euler (R ⧸ Ideal.span {r})
        (ModuleCat.of (R ⧸ Ideal.span {r})
          ((R ⧸ Ideal.span {r}) ⧸ Ideal.ofList (rs.map (algebraMap R (R ⧸ Ideal.span {r})))))
        (ModuleCat.of (R ⧸ Ideal.span {r}) (QuotSMulTop r N)) d :=
  (IsolatedEuler.euler_iso_left R (restrictedSequenceQuotientIso R r rs).symm N d).trans
    (ElementChangeOfRings.Regular.euler_eq R r N _ hr hn d)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.SequenceChangeOfRings
