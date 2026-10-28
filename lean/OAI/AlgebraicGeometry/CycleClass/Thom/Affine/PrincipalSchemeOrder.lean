import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularOrder
import OAI.AlgebraicGeometry.CycleClass.Thom.RationalOrderTransport

/-! # Principal Scheme Order -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PrincipalSchemeOrder.Constructions

noncomputable section

/-! On an arbitrary integral Noetherian affine scheme, the order of
the actual rational function coming from a ring element is its native
localized principal-quotient length. Normality is not required. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false

universe u
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]

local instance : Algebra R (Spec (CommRingCat.of R)).functionField :=
  (StructureSheaf.toStalk R (genericPoint (Spec (CommRingCat.of R)))).hom.toAlgebra

local instance (p : Spec (CommRingCat.of R)) : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk p) :=
  StructureSheaf.stalkAlgebra R p

local instance (p : Spec (CommRingCat.of R)) : p.asIdeal.IsPrime :=
  (show PrimeSpectrum R from p).isPrime

def affineFunction (a : R) : (Spec (CommRingCat.of R)).functionField :=
  algebraMap R (Spec (CommRingCat.of R)).functionField a

omit [IsNoetherianRing R] in
theorem stalkField_tower (p : Spec (CommRingCat.of R)) :
    IsScalarTower R ((Spec (CommRingCat.of R)).presheaf.stalk p) (Spec (CommRingCat.of R)).functionField := by
  apply IsScalarTower.of_algebraMap_eq'
  exact (congrArg CommRingCat.Hom.hom
    (StructureSheaf.toStalk_stalkSpecializes
      ((genericPoint_spec (Spec (CommRingCat.of R))).specializes trivial))).symm

theorem schemeOrder_eq_localOrder (p : Spec (CommRingCat.of R)) (hp : p.asIdeal.height = 1)
    (a : R) (ha : a ≠ 0) :
    (Spec (CommRingCat.of R)).ord (affineFunction R a) p =
      ((Ring.ord (Localization.AtPrime p.asIdeal) (algebraMap R (Localization.AtPrime p.asIdeal) a)).toNat : ℤ) := by
  let := stalkField_tower R p
  have hheight : Order.coheight (show Spec (CommRingCat.of R) from p) = 1 :=
    (idealHeight_eq_coheight (CommRingCat.of R) p).symm.trans hp
  let e : Localization.AtPrime p.asIdeal ≃ₐ[R] ((Spec (CommRingCat.of R)).presheaf.stalk p) :=
    StructureSheaf.stalkIso R (show PrimeSpectrum R from p)
  have hne : algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk p) a ≠ 0 := by
    rw [← e.commutes a]
    exact (map_ne_zero_iff _ e.injective).mpr
      ((map_ne_zero_iff _ (IsLocalization.injective (Localization.AtPrime p.asIdeal)
        p.asIdeal.primeCompl_le_nonZeroDivisors)).mpr ha)
  rw [affineFunction, IsScalarTower.algebraMap_apply R ((Spec (CommRingCat.of R)).presheaf.stalk p)
    (Spec (CommRingCat.of R)).functionField,
    Scheme.RegularOrder.Constructions.ord_algebraMap_stalk _ p hheight _ hne]
  have he := RationalOrderTransport.Constructions.ringOrder_equiv e.toRingEquiv
    (algebraMap R (Localization.AtPrime p.asIdeal) a)
  change Ring.ord _ (e (algebraMap R (Localization.AtPrime p.asIdeal) a)) = _ at he
  rw [AlgEquiv.commutes] at he
  exact congrArg (fun l : ℕ∞ => (l.toNat : ℤ)) he

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PrincipalSchemeOrder.Constructions
