import OAI.AlgebraicGeometry.CycleClass.Thom.Open.StalkSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.QuotientBaseChange

/-! # Support Tor -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportTor

noncomputable section

/-! Every native local Tor length of two reduced supports is unchanged
on an open component. The comparison uses their actual defining primes
and the actual isomorphism of ambient stalk rings. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions

universe u

theorem localTorLength_congr_point (X : Scheme) (A B : IrreducibleCloseds X)
    {x y : X} (h : x = y) (hxA : x ∈ (A : Set X)) (hxB : x ∈ (B : Set X))
    (hyA : y ∈ (A : Set X)) (hyB : y ∈ (B : Set X)) (n : ℕ) :
    IntersectionGeometry.localTorLength X A B x hxA hxB n = IntersectionGeometry.localTorLength X A B y hyA hyB n := by
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
    (hA : i (IntersectionGeometry.supportPoint A) = IntersectionGeometry.supportPoint A') (hB : i (IntersectionGeometry.supportPoint B) = IntersectionGeometry.supportPoint B')
    (y : Y) (hyA : y ∈ (A : Set Y)) (hyB : y ∈ (B : Set Y))
    (hxA : i y ∈ (A' : Set X)) (hxB : i y ∈ (B' : Set X)) (n : ℕ) :
    IntersectionGeometry.localTorLength Y A B y hyA hyB n = IntersectionGeometry.localTorLength X A' B' (i y) hxA hxB n := by
  let R := X.presheaf.stalk (i y)
  let S := Y.presheaf.stalk y
  let : Algebra R S := (i.stalkMap y).hom.toAlgebra
  have hi : Function.Surjective (algebraMap R S) :=
    (ConcreteCategory.bijective_of_isIso (i.stalkMap y)).surjective
  let : IsLocalHom (algebraMap R S) := IsLocalHom.of_surjective _ hi
  let e : R ≃ₐ[R] S :=
    { (asIso (i.stalkMap y)).commRingCatIsoToRingEquiv with commutes' := fun _ => rfl }
  let : Module.Flat R S := Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  let pA := StalkPrimeQuotient.Constructions.kernelPrime X A' (i y) hxA
  let pB := StalkPrimeQuotient.Constructions.kernelPrime X B' (i y) hxB
  let qA := StalkPrimeQuotient.Constructions.kernelPrime Y A y hyA
  let qB := StalkPrimeQuotient.Constructions.kernelPrime Y B y hyB
  have hX := length_iso R
    (StalkPrimeQuotient.Constructions.moduleEquiv X A' (i y) hxA pA (StalkPrimeQuotient.Constructions.kernelPrime_image X A' (i y) hxA)).toModuleIso
    (StalkPrimeQuotient.Constructions.moduleEquiv X B' (i y) hxB pB (StalkPrimeQuotient.Constructions.kernelPrime_image X B' (i y) hxB)).toModuleIso n
  have hY := length_iso S
    (StalkPrimeQuotient.Constructions.moduleEquiv Y A y hyA qA (StalkPrimeQuotient.Constructions.kernelPrime_image Y A y hyA)).toModuleIso
    (StalkPrimeQuotient.Constructions.moduleEquiv Y B y hyB qB (StalkPrimeQuotient.Constructions.kernelPrime_image Y B y hyB)).toModuleIso n
  have hpA : pA.asIdeal.map (algebraMap R S) = qA.asIdeal :=
    StalkSupport.Constructions.kernelPrime_map i A A' hA y hyA hxA
  have hpB : pB.asIdeal.map (algebraMap R S) = qB.asIdeal :=
    StalkSupport.Constructions.kernelPrime_map i B B' hB y hyB hxB
  change Module.length S (((Tor (ModuleCat S) n).obj (IntersectionGeometry.localSupportModule Y A y hyA)).obj
      (IntersectionGeometry.localSupportModule Y B y hyB)) =
    Module.length R (((Tor (ModuleCat R) n).obj (IntersectionGeometry.localSupportModule X A' (i y) hxA)).obj
      (IntersectionGeometry.localSupportModule X B' (i y) hxB))
  rw [hY, hX, ← hpA, ← hpB]
  exact TorAlgebra.QuotientBaseChange.Tor.length_eq R S pA.asIdeal pB.asIdeal n
    (IsLocalRing.map_maximalIdeal_of_surjective _ hi)

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportTor
