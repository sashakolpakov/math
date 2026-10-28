import Mathlib

/-! # Flat Coefficient Sheaves -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FlatCoefficientSheaves

noncomputable section

/-!
# IntegralComparison: exact restriction along flat coefficient extensions

For a flat extension of coefficient rings, extension of coefficients
preserves monomorphisms. The induced sheaf adjunction therefore shows
that restriction preserves injectives, as well as exact sequences.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

variable (S R : Type u) [CommRing S] [CommRing R] [Algebra S R]

abbrev extendCoefficients : ModuleCat.{u} S ⥤ ModuleCat.{u} R :=
  ModuleCat.extendScalars (algebraMap S R)

instance extendCoefficients_preservesFiniteLimits [Module.Flat S R] :
    PreservesFiniteLimits (extendCoefficients S R) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat (RingHom.flat_algebraMap_iff.mpr inferInstance)

instance extendCoefficients_preservesMonos [Module.Flat S R] :
    (extendCoefficients S R).PreservesMonomorphisms := by infer_instance

variable {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
  [HasSheafify J (ModuleCat.{u} S)] [HasSheafify J (ModuleCat.{u} R)]

abbrev extension : Sheaf J (ModuleCat.{u} S) ⥤ Sheaf J (ModuleCat.{u} R) :=
  Sheaf.composeAndSheafify J (extendCoefficients S R)

abbrev restriction : Sheaf J (ModuleCat.{u} R) ⥤ Sheaf J (ModuleCat.{u} S) :=
  sheafCompose J (ModuleCat.restrictScalars (algebraMap S R))

def adjunction : extension S R J ⊣ restriction S R J :=
  Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj (algebraMap S R))

instance extension_preservesMonos [Module.Flat S R] : (extension S R J).PreservesMonomorphisms where
  preserves {M N} a ha := by
    have : Mono a.hom := inferInstanceAs (Mono ((sheafToPresheaf J (ModuleCat.{u} S)).map a))
    have : Mono (Functor.whiskerRight a.hom (extendCoefficients S R)) := by
      apply NatTrans.mono_of_mono_app
    exact Functor.map_mono (presheafToSheaf J (ModuleCat.{u} R))
      (Functor.whiskerRight a.hom (extendCoefficients S R))

instance restriction_preservesInjectives [Module.Flat S R] :
    (restriction S R J).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (FlatCoefficientSheaves.adjunction S R J)

def restrictionIso :
    Sheaf.composeAndSheafify J (ModuleCat.restrictScalars (algebraMap S R)) ≅ restriction S R J :=
  Functor.isoWhiskerLeft (sheafToPresheaf _ _)
      (sheafComposeNatIso J (ModuleCat.restrictScalars (algebraMap S R))
        (sheafificationAdjunction _ _) (sheafificationAdjunction _ _)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (sheafificationAdjunction _ _).counit) _ ≪≫
    Functor.leftUnitor _

instance restriction_preservesFiniteLimits : PreservesFiniteLimits (restriction S R J) := by
  have := (FlatCoefficientSheaves.adjunction S R J).isRightAdjoint
  infer_instance

instance restriction_preservesFiniteColimits : PreservesFiniteColimits (restriction S R J) := by
  have := (Sheaf.adjunction J (ModuleCat.restrictCoextendScalarsAdj (algebraMap S R))).isLeftAdjoint
  exact preservesFiniteColimits_of_natIso (restrictionIso S R J)

instance restriction_additive : (restriction S R J).Additive where
  map_add := by
    intro M N a b
    apply Sheaf.hom_ext
    ext U x
    rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FlatCoefficientSheaves
