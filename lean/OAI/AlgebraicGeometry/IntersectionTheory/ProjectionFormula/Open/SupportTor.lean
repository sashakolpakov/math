import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.StalkSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.QuotientTorBaseChange

/-! # Support Tor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportTor

noncomputable section

/-! Every native local Tor length of two reduced supports is unchanged
on an open component. The comparison uses their actual defining primes
and the actual isomorphism of ambient stalk rings. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient

universe u

theorem localTorLength_congr_point (X : Scheme) (A B : IrreducibleCloseds X)
    {x y : X} (h : x = y) (hxA : x ∈ (A : Set X)) (hxB : x ∈ (B : Set X))
    (hyA : y ∈ (A : Set X)) (hyB : y ∈ (B : Set X)) (n : ℕ) :
    CycleClass.Thom.IntersectionGeometry.localTorLength X A B x hxA hxB n = CycleClass.Thom.IntersectionGeometry.localTorLength X A B y hyA hyB n := by
  subst y
  rfl

theorem length_iso (R : Type u) [CommRing R] {M M' N N' : ModuleCat.{u} R}
    (eM : M ≅ M') (eN : N ≅ N') (n : ℕ) :
    Module.length R (((Tor (ModuleCat R) n).obj M).obj N) =
      Module.length R (((Tor (ModuleCat R) n).obj M').obj N') :=
  ((((Tor (ModuleCat R) n).mapIso eM).app N) ≪≫
    (((Tor (ModuleCat R) n).obj M').mapIso eN)).toLinearEquiv.length_eq

theorem localTorLength_eq {Y X : Scheme} (i : Y ⟶ X) [IsOpenImmersion i]
    (A B : IrreducibleCloseds Y) (A' B' : IrreducibleCloseds X)
    (hA : i (CycleClass.Thom.IntersectionGeometry.supportPoint A) = CycleClass.Thom.IntersectionGeometry.supportPoint A') (hB : i (CycleClass.Thom.IntersectionGeometry.supportPoint B) = CycleClass.Thom.IntersectionGeometry.supportPoint B')
    (y : Y) (hyA : y ∈ (A : Set Y)) (hyB : y ∈ (B : Set Y))
    (hxA : i y ∈ (A' : Set X)) (hxB : i y ∈ (B' : Set X)) (n : ℕ) :
    CycleClass.Thom.IntersectionGeometry.localTorLength Y A B y hyA hyB n = CycleClass.Thom.IntersectionGeometry.localTorLength X A' B' (i y) hxA hxB n := by
  let R := X.presheaf.stalk (i y)
  let S := Y.presheaf.stalk y
  let : Algebra R S := (i.stalkMap y).hom.toAlgebra
  have hi : Function.Surjective (algebraMap R S) :=
    (ConcreteCategory.bijective_of_isIso (i.stalkMap y)).surjective
  let : IsLocalHom (algebraMap R S) := IsLocalHom.of_surjective _ hi
  let e : R ≃ₐ[R] S :=
    { (asIso (i.stalkMap y)).commRingCatIsoToRingEquiv with commutes' := fun _ => rfl }
  let : Module.Flat R S := Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  let pA := Stalk.PrimeQuotient.kernelPrime X A' (i y) hxA
  let pB := Stalk.PrimeQuotient.kernelPrime X B' (i y) hxB
  let qA := Stalk.PrimeQuotient.kernelPrime Y A y hyA
  let qB := Stalk.PrimeQuotient.kernelPrime Y B y hyB
  have hX := length_iso R
    (Stalk.PrimeQuotient.moduleEquiv X A' (i y) hxA pA (Stalk.PrimeQuotient.kernelPrime_image X A' (i y) hxA)).toModuleIso
    (Stalk.PrimeQuotient.moduleEquiv X B' (i y) hxB pB (Stalk.PrimeQuotient.kernelPrime_image X B' (i y) hxB)).toModuleIso n
  have hY := length_iso S
    (Stalk.PrimeQuotient.moduleEquiv Y A y hyA qA (Stalk.PrimeQuotient.kernelPrime_image Y A y hyA)).toModuleIso
    (Stalk.PrimeQuotient.moduleEquiv Y B y hyB qB (Stalk.PrimeQuotient.kernelPrime_image Y B y hyB)).toModuleIso n
  have hpA : pA.asIdeal.map (algebraMap R S) = qA.asIdeal :=
    StalkSupport.kernelPrime_map i A A' hA y hyA hxA
  have hpB : pB.asIdeal.map (algebraMap R S) = qB.asIdeal :=
    StalkSupport.kernelPrime_map i B B' hB y hyB hxB
  change Module.length S (((Tor (ModuleCat S) n).obj (CycleClass.Thom.IntersectionGeometry.localSupportModule Y A y hyA)).obj
      (CycleClass.Thom.IntersectionGeometry.localSupportModule Y B y hyB)) =
    Module.length R (((Tor (ModuleCat R) n).obj (CycleClass.Thom.IntersectionGeometry.localSupportModule X A' (i y) hxA)).obj
      (CycleClass.Thom.IntersectionGeometry.localSupportModule X B' (i y) hxB))
  rw [hY, hX, ← hpA, ← hpB]
  exact QuotientTorBaseChange.length_eq R S pA.asIdeal pB.asIdeal n
    (IsLocalRing.map_maximalIdeal_of_surjective _ hi)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportTor
