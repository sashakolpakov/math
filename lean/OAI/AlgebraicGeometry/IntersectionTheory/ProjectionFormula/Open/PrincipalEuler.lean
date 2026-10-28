import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportBaseChange
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportTor

/-! # Principal Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.PrincipalEuler

noncomputable section

/-! A principal-quotient Euler pairing is unchanged under an open
immersion, with the native modules and the native ambient stalk map. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem euler {Y X : Scheme} (j : Y ⟶ X) [IsOpenImmersion j]
    (A B : IrreducibleCloseds Y) (A' B' : IrreducibleCloseds X)
    (hA : j (CycleClass.Thom.IntersectionGeometry.supportPoint A) = CycleClass.Thom.IntersectionGeometry.supportPoint A') (hB : j (CycleClass.Thom.IntersectionGeometry.supportPoint B) = CycleClass.Thom.IntersectionGeometry.supportPoint B')
    (y : Y) (hyA : y ∈ (A : Set Y)) (hyB : y ∈ (B : Set Y))
    (hxA : j y ∈ (A' : Set X)) (hxB : j y ∈ (B' : Set X))
    (r : X.presheaf.stalk (j y)) (d : ℕ) :
    Tor.Euler.euler (Y.presheaf.stalk y)
      (.of _ (QuotSMulTop (j.stalkMap y r) (CycleClass.Thom.IntersectionGeometry.localSupportModule Y A y hyA)))
      (CycleClass.Thom.IntersectionGeometry.localSupportModule Y B y hyB) d =
    Tor.Euler.euler (X.presheaf.stalk (j y))
      (.of _ (QuotSMulTop r (CycleClass.Thom.IntersectionGeometry.localSupportModule X A' (j y) hxA)))
      (CycleClass.Thom.IntersectionGeometry.localSupportModule X B' (j y) hxB) d := by
  let R := X.presheaf.stalk (j y)
  let S := Y.presheaf.stalk y
  let : Algebra R S := (j.stalkMap y).hom.toAlgebra
  have hi : Function.Surjective (algebraMap R S) :=
    (ConcreteCategory.bijective_of_isIso (j.stalkMap y)).surjective
  let : IsLocalHom (algebraMap R S) := IsLocalHom.of_surjective _ hi
  let e : R ≃ₐ[R] S :=
    { (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv with commutes' := fun _ => rfl }
  let : Module.Flat R S := Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  let eM := SupportBaseChange.quotientEquiv j A A' hA y hyA hxA r
  let eN := SupportBaseChange.equiv j B B' hB y hyB hxB
  apply Finset.sum_congr rfl
  intro n _
  apply congrArg (fun l : ℕ∞ => (-1 : ℚ) ^ n * (l.toNat : ℚ))
  rw [SupportTor.length_iso S eM.symm.toModuleIso eN.symm.toModuleIso n]
  have hl := ProjectionFormula.Flat.TorLength.tor_length R S (.of R (QuotSMulTop r (CycleClass.Thom.IntersectionGeometry.localSupportModule X A' (j y) hxA)))
    (CycleClass.Thom.IntersectionGeometry.localSupportModule X B' (j y) hxB) n
  rw [IsLocalRing.map_maximalIdeal_of_surjective _ hi,
    SurfacePrimeEuler.residue_quotient_length, mul_one] at hl
  exact hl

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.PrincipalEuler
