import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizedBranchOrder

/-! # Affine Order -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normal.AffineOrder.Constructions.NormalizationLocal

noncomputable section

/-!
# ThomClass: normal-branch orders are actual affine scheme orders

The spectrum's generic field and its stalks are identified through the
canonical fraction-field and localization maps. This identifies each
normal branch's algebraic order with Scheme.ord at the corresponding
point, using the default elaborator settings.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory IsDedekindDomain _root_.Order

open OAI.AlgebraicGeometry.CycleClass.Thom.RationalOrderTransport.Constructions

universe u
variable (S : Type u) [CommRing S] [IsDedekindDomain S]

local instance : Algebra S (Spec (CommRingCat.of S)).functionField :=
  (StructureSheaf.toStalk S (genericPoint (Spec (CommRingCat.of S)))).hom.toAlgebra

local instance (x : Spec (CommRingCat.of S)) : Algebra S ((Spec (CommRingCat.of S)).presheaf.stalk x) :=
  StructureSheaf.stalkAlgebra S x

local instance : IsFractionRing S (Spec (CommRingCat.of S)).functionField :=
  functionField_isFractionRing_of_affine (CommRingCat.of S)

abbrev normalBranchPoint (P : HeightOneSpectrum S) : Spec (CommRingCat.of S) := ⟨P.asIdeal, P.isPrime⟩

theorem normalBranchPoint_coheight (P : HeightOneSpectrum S) : coheight (normalBranchPoint S P) = 1 := by
  rw [← idealHeight_eq_coheight]
  change P.asIdeal.height = 1
  apply le_antisymm
  · exact WithBot.coe_le_coe.mp
      (P.asIdeal.height_le_ringKrullDim_of_isPrime.trans (Order.KrullDimLE.krullDim_le (n := 1)))
  · exact Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr P.ne_bot)

def normalAffineFieldIso : FractionRing S ≃ₐ[S] (Spec (CommRingCat.of S)).functionField :=
  FractionRing.algEquiv S (Spec (CommRingCat.of S)).functionField

def normalAffineStalkIso (x : Spec (CommRingCat.of S)) :
    letI : x.asIdeal.IsPrime := (show PrimeSpectrum S from x).isPrime
    Localization.AtPrime x.asIdeal ≃ₐ[S] (Spec (CommRingCat.of S)).presheaf.stalk x := by
  let : x.asIdeal.IsPrime := (show PrimeSpectrum S from x).isPrime
  exact StructureSheaf.stalkIso S (show PrimeSpectrum S from x)

theorem normalAffine_stalkField_tower (x : Spec (CommRingCat.of S)) :
    IsScalarTower S ((Spec (CommRingCat.of S)).presheaf.stalk x) (Spec (CommRingCat.of S)).functionField := by
  apply IsScalarTower.of_algebraMap_eq'
  exact (congrArg CommRingCat.Hom.hom
    (StructureSheaf.toStalk_stalkSpecializes ((genericPoint_spec (Spec (CommRingCat.of S))).specializes trivial))).symm

theorem normalAffineFieldIso_stalk (P : HeightOneSpectrum S) (a : Localization.AtPrime P.asIdeal) :
    normalAffineFieldIso S (algebraMap (Localization.AtPrime P.asIdeal) (FractionRing S) a) =
      algebraMap ((Spec (CommRingCat.of S)).presheaf.stalk (normalBranchPoint S P))
        (Spec (CommRingCat.of S)).functionField (normalAffineStalkIso S (normalBranchPoint S P) a) := by
  let := normalAffine_stalkField_tower S (normalBranchPoint S P)
  have he : (normalAffineFieldIso S).toRingHom.comp (algebraMap (Localization.AtPrime P.asIdeal) (FractionRing S)) =
      (algebraMap ((Spec (CommRingCat.of S)).presheaf.stalk (normalBranchPoint S P))
        (Spec (CommRingCat.of S)).functionField).comp (normalAffineStalkIso S (normalBranchPoint S P)).toRingHom := by
    apply IsLocalization.ringHom_ext P.asIdeal.primeCompl
    ext s
    change normalAffineFieldIso S
      (algebraMap (Localization.AtPrime P.asIdeal) (FractionRing S) (algebraMap S (Localization.AtPrime P.asIdeal) s)) =
      algebraMap ((Spec (CommRingCat.of S)).presheaf.stalk (normalBranchPoint S P))
        (Spec (CommRingCat.of S)).functionField (normalAffineStalkIso S (normalBranchPoint S P) (algebraMap S _ s))
    rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  exact congrArg (fun h => h a) he

theorem schemeOrder_eq_normalBranchOrder (P : HeightOneSpectrum S) (g : FractionRing S) :
    (Spec (CommRingCat.of S)).ord (normalAffineFieldIso S g) (normalBranchPoint S P) =
      SemilocalDivisorNorm.Constructions.localOrder P g := by
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S P.ne_bot (Localization.AtPrime P.asIdeal)
  let : Ring.KrullDimLE 1 ((Spec (CommRingCat.of S)).presheaf.stalk (normalBranchPoint S P)) :=
    krullDimLE_of_coheight_le (normalBranchPoint_coheight S P).le
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one (normalBranchPoint_coheight S P)]
  exact congrArg (fun z : WithZero (Multiplicative ℤ) => Multiplicative.toAdd (z.unzeroD 1))
    (RationalOrderTransport.Constructions.ringOrderFrac_equiv (normalAffineStalkIso S (normalBranchPoint S P)).toRingEquiv
      (normalAffineFieldIso S).toRingEquiv (normalAffineFieldIso_stalk S P) g)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normal.AffineOrder.Constructions.NormalizationLocal
