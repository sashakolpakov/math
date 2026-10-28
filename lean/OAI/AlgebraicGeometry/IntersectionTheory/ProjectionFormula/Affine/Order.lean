import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SemilocalDivisorNorm
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.OrderQuotientTransport
import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-! # Order -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.Order

noncomputable section

/-! The affine orders in the norm calculation agree with the actual scheme
orders, through the canonical stalk and function-field isomorphisms. -/

set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry IsDedekindDomain _root_.Order

universe u

variable (S : Type u) [CommRing S] [IsDedekindDomain S]

local instance : Algebra S (Spec (.of S)).functionField :=
  (StructureSheaf.toStalk S (genericPoint (Spec (.of S)))).hom.toAlgebra

local instance (x : Spec (.of S)) : Algebra S ((Spec (.of S)).presheaf.stalk x) :=
  StructureSheaf.stalkAlgebra S x

local instance : IsFractionRing S (Spec (.of S)).functionField :=
  functionField_isFractionRing_of_affine (CommRingCat.of S)

abbrev branchPoint (P : HeightOneSpectrum S) : Spec (CommRingCat.of S) :=
  ⟨P.asIdeal, P.isPrime⟩

theorem branchPoint_coheight (P : HeightOneSpectrum S) :
    coheight (branchPoint S P) = 1 := by
  rw [← idealHeight_eq_coheight]
  change P.asIdeal.height = 1
  apply le_antisymm
  · exact WithBot.coe_le_coe.mp
      (P.asIdeal.height_le_ringKrullDim_of_isPrime.trans (Order.KrullDimLE.krullDim_le (n := 1)))
  · exact Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr P.ne_bot)

def affineFunctionFieldIso : FractionRing S ≃ₐ[S] (Spec (.of S)).functionField :=
  FractionRing.algEquiv S (Spec (.of S)).functionField

def affineStalkIso (x : Spec (.of S)) :
    Localization.AtPrime x.asIdeal ≃ₐ[S] (Spec (.of S)).presheaf.stalk x :=
  StructureSheaf.stalkIso S x

theorem affine_stalk_functionField_tower (x : Spec (.of S)) :
    IsScalarTower S ((Spec (.of S)).presheaf.stalk x) (Spec (.of S)).functionField := by
  apply IsScalarTower.of_algebraMap_eq'
  exact (congrArg CommRingCat.Hom.hom
    (StructureSheaf.toStalk_stalkSpecializes
      ((genericPoint_spec (Spec (.of S))).specializes trivial))).symm

theorem affineFunctionFieldIso_stalk (P : HeightOneSpectrum S)
    (a : Localization.AtPrime P.asIdeal) :
    affineFunctionFieldIso S (algebraMap (Localization.AtPrime P.asIdeal) (FractionRing S) a) =
      algebraMap ((Spec (.of S)).presheaf.stalk (branchPoint S P))
        (Spec (.of S)).functionField (affineStalkIso S (branchPoint S P) a) := by
  let := affine_stalk_functionField_tower S (branchPoint S P)
  have h : (affineFunctionFieldIso S).toRingHom.comp
      (algebraMap (Localization.AtPrime P.asIdeal) (FractionRing S)) =
      (algebraMap ((Spec (.of S)).presheaf.stalk (branchPoint S P))
        (Spec (.of S)).functionField).comp
          (affineStalkIso S (branchPoint S P)).toRingHom := by
    apply IsLocalization.ringHom_ext P.asIdeal.primeCompl
    ext s
    change affineFunctionFieldIso S
      (algebraMap (Localization.AtPrime P.asIdeal) (FractionRing S)
        (algebraMap S (Localization.AtPrime P.asIdeal) s)) =
      algebraMap ((Spec (.of S)).presheaf.stalk (branchPoint S P))
        (Spec (.of S)).functionField
          (affineStalkIso S (branchPoint S P) (algebraMap S _ s))
    rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
  exact congrArg (fun h => h a) h

theorem schemeOrder_eq_localOrder (P : HeightOneSpectrum S) (f : FractionRing S) :
    (Spec (.of S)).ord (affineFunctionFieldIso S f) (branchPoint S P) =
      SemilocalDivisorNorm.localOrder P f := by
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    S P.ne_bot (Localization.AtPrime P.asIdeal)
  let : Ring.KrullDimLE 1 ((Spec (.of S)).presheaf.stalk (branchPoint S P)) :=
    krullDimLE_of_coheight_le (branchPoint_coheight S P).le
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one (branchPoint_coheight S P)]
  change WithZero.log (Ring.ordFrac ((Spec (.of S)).presheaf.stalk (branchPoint S P))
    (affineFunctionFieldIso S f)) = _
  exact congrArg WithZero.log (OrderQuotientTransport.ordFrac_equiv
    (affineStalkIso S (branchPoint S P)).toRingEquiv
    (affineFunctionFieldIso S).toRingEquiv (affineFunctionFieldIso_stalk S P) f)

/-- The unique closed branch of the spectrum of a DVR. -/
def closedBranch [IsDiscreteValuationRing S] : HeightOneSpectrum S :=
  ⟨IsLocalRing.maximalIdeal S, inferInstance,
    Ring.ne_bot_of_isMaximal_of_not_isField inferInstance
      (IsDiscreteValuationRing.not_isField S)⟩

theorem schemeOrder_closed [IsDiscreteValuationRing S] (f : FractionRing S) :
    (Spec (.of S)).ord (affineFunctionFieldIso S f)
      (branchPoint S (closedBranch S)) = WithZero.log (Ring.ordFrac S f) := by
  rw [schemeOrder_eq_localOrder]
  let A := Localization.AtPrime (IsLocalRing.maximalIdeal S)
  let e : S ≃ₐ[S] A := IsLocalization.atUnits S (IsLocalRing.maximalIdeal S).primeCompl (by
    intro s hs
    exact IsLocalRing.notMem_maximalIdeal.mp hs)
  have hc (s : S) : algebraMap S (FractionRing S) s =
      algebraMap A (FractionRing S) (e s) := by
    have he : e s = algebraMap S A s := by simpa using e.commutes s
    rw [he, ← IsScalarTower.algebraMap_apply]
  exact congrArg WithZero.log (OrderQuotientTransport.ordFrac_equiv e.toRingEquiv
    (RingEquiv.refl (FractionRing S)) hc f)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.Order
