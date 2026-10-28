import OAI.AlgebraicGeometry.SheafCohomology.ExtAdjunction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafUniverses
import Mathlib
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Sheaf Coefficient Adjunction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.SheafCoefficientAdjunction.IntegralSheafCoefficientAdjunction

noncomputable section

/-! Exact integral coefficient adjunction for flat commutative coefficient rings on small sites. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable (R : Type) [CommRing R] [Module.Flat ℤ R]

abbrev extendCoefficients : ModuleCat.{0} ℤ ⥤ ModuleCat.{0} R :=
  ModuleCat.extendScalars.{0, 0, 0} (Int.castRingHom R)

abbrev restrictCoefficients : ModuleCat.{0} R ⥤ ModuleCat.{0} ℤ :=
  ModuleCat.restrictScalars.{0, 0, 0} (Int.castRingHom R)

abbrev coextendCoefficients : ModuleCat.{0} ℤ ⥤ ModuleCat.{0} R :=
  ModuleCat.coextendScalars.{0, 0, 0} (Int.castRingHom R)

def coefficientAdjunction : extendCoefficients R ⊣ restrictCoefficients R :=
  ModuleCat.extendRestrictScalarsAdj.{0, 0, 0} (Int.castRingHom R)

def coefficientCoAdjunction : restrictCoefficients R ⊣ coextendCoefficients R :=
  ModuleCat.restrictCoextendScalarsAdj.{0, 0, 0} (Int.castRingHom R)

instance coextendCoefficients_rightAdjoint : (coextendCoefficients R).IsRightAdjoint :=
  (coefficientCoAdjunction R).isRightAdjoint

instance extendCoefficients_leftAdjoint : (extendCoefficients R).IsLeftAdjoint :=
  (coefficientAdjunction R).isLeftAdjoint

instance restrictCoefficients_rightAdjoint : (restrictCoefficients R).IsRightAdjoint :=
  (coefficientAdjunction R).isRightAdjoint

instance restrictCoefficients_leftAdjoint : (restrictCoefficients R).IsLeftAdjoint :=
  (coefficientCoAdjunction R).isLeftAdjoint

instance extendCoefficients_preservesMonos : (extendCoefficients R).PreservesMonomorphisms where
  preserves {M N} f hf := by
    apply (ModuleCat.mono_iff_injective _).mpr
    change Function.Injective
      (@LinearMap.baseChange ℤ R M N _ _
        ((algebraMap R R).comp (Int.castRingHom R)).toAlgebra _ _ _ _ f.hom)
    rw [Subsingleton.elim
      ((algebraMap R R).comp (Int.castRingHom R)).toAlgebra (inferInstance : Algebra ℤ R)]
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := R) f.hom
      ((ModuleCat.mono_iff_injective f).mp hf)

variable {C : Type} [Category.{0} C] (J : GrothendieckTopology C)

instance integerSheafify : HasSheafify J (ModuleCat.{0} ℤ) :=
  HasSheafify.mk' _ _ (plusPlusAdjunction J (ModuleCat.{0} ℤ))

abbrev extendSheaf : Sheaf J (ModuleCat.{0} ℤ) ⥤ Sheaf J (ModuleCat.{0} R) :=
  Sheaf.composeAndSheafify J (extendCoefficients R)

abbrev restrictSheaf : Sheaf J (ModuleCat.{0} R) ⥤ Sheaf J (ModuleCat.{0} ℤ) :=
  sheafCompose J (restrictCoefficients R)

def adjunction : extendSheaf R J ⊣ restrictSheaf R J :=
  Sheaf.adjunction J (coefficientAdjunction R)

instance extendSheaf_preservesMonos : (extendSheaf R J).PreservesMonomorphisms where
  preserves {M N} f hf := by
    let : Mono f.hom := presheaf_mono_of_mono _ _ f
    let : Mono (Functor.whiskerRight f.hom (extendCoefficients R)) := by
      apply NatTrans.mono_of_mono_app
    exact Functor.map_mono (presheafToSheaf J (ModuleCat.{0} R))
      (Functor.whiskerRight f.hom (extendCoefficients R))

instance restrictSheaf_preservesInjectives : (restrictSheaf R J).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (IntegralSheafCoefficientAdjunction.adjunction R J)

def restrictSheafIso : Sheaf.composeAndSheafify J
    (restrictCoefficients R) ≅ restrictSheaf R J :=
  Functor.isoWhiskerLeft (sheafToPresheaf _ _)
      (sheafComposeNatIso J (restrictCoefficients R)
        (sheafificationAdjunction _ _) (sheafificationAdjunction _ _)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (sheafificationAdjunction _ _).counit) _ ≪≫
    Functor.leftUnitor _

instance restrictSheaf_preservesFiniteLimits : PreservesFiniteLimits (restrictSheaf R J) := by
  let := (IntegralSheafCoefficientAdjunction.adjunction R J).isRightAdjoint
  infer_instance

instance restrictSheaf_preservesFiniteColimits : PreservesFiniteColimits (restrictSheaf R J) := by
  let := (Sheaf.adjunction J
    (coefficientCoAdjunction R)).isLeftAdjoint
  exact preservesFiniteColimits_of_natIso (restrictSheafIso R J)

instance restrictSheaf_additive : (restrictSheaf R J).Additive where
  map_add := by
    intro M N f g
    apply Sheaf.hom_ext
    ext U x
    rfl

instance moduleSheafGrothendieck : IsGrothendieckAbelian.{0} (Sheaf J (ModuleCat.{0} R)) :=
  IntegralComparison.Module.SheafUniverses.isGrothendieckAbelian.{0, 0, 0} J R

universe w w'

def extAdjunction
    [HasExt.{w} (Sheaf J (ModuleCat.{0} ℤ))] [HasExt.{w'} (Sheaf J (ModuleCat.{0} R))]
    (M : Sheaf J (ModuleCat.{0} ℤ)) (N : Sheaf J (ModuleCat.{0} R)) (n : ℕ) :
    Abelian.Ext.{w'} ((extendSheaf R J).obj M) N n ≃+
      Abelian.Ext.{w} M ((restrictSheaf R J).obj N) n :=
  AlgebraicGeometry.SheafCohomology.ExtAdjunction.Projective.extAdjunction (restrictSheaf R J) M (IntegralSheafCoefficientAdjunction.adjunction R J) N n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.SheafCoefficientAdjunction.IntegralSheafCoefficientAdjunction
