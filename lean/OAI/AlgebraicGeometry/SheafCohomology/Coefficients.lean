import OAI.AlgebraicGeometry.SheafCohomology.CoefficientFlatness
import OAI.AlgebraicGeometry.SheafCohomology.Sheaves
import OAI.AlgebraicGeometry.SheafCohomology.ExtAdjunction
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Coefficients -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Coefficients.Projective

noncomputable section

/-! Change from integral to complex coefficients for actual sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

abbrev extendComplexSheaf (X : TopCat.{0}) :=
  Sheaf.composeAndSheafify (Opens.grothendieckTopology X) CoefficientFlatness.Projective.extendComplexCoefficients

abbrev restrictComplexSheaf (X : TopCat.{0}) :=
  sheafCompose (Opens.grothendieckTopology X)
    (ModuleCat.restrictScalars (Int.castRingHom ℂ))

def complexSheafAdjunction (X : TopCat.{0}) :
    extendComplexSheaf X ⊣ restrictComplexSheaf X :=
  Sheaf.adjunction (Opens.grothendieckTopology X)
    (ModuleCat.extendRestrictScalarsAdj (Int.castRingHom ℂ))

instance extendComplexSheaf_preservesMonos (X : TopCat.{0}) :
    (extendComplexSheaf X).PreservesMonomorphisms where
  preserves {M N} f hf := by
    have hmono : Mono f.hom := presheaf_mono_of_mono _ _ f
    have hwhisker : Mono (Functor.whiskerRight f.hom CoefficientFlatness.Projective.extendComplexCoefficients) := by
      apply NatTrans.mono_of_mono_app
    exact Functor.map_mono
      (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat ℂ))
      (Functor.whiskerRight f.hom CoefficientFlatness.Projective.extendComplexCoefficients)

instance restrictComplexSheaf_preservesInjectives (X : TopCat.{0}) :
    (restrictComplexSheaf X).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (complexSheafAdjunction X)

def restrictComplexSheafIso (X : TopCat.{0}) :
    Sheaf.composeAndSheafify (Opens.grothendieckTopology X)
      (ModuleCat.restrictScalars (Int.castRingHom ℂ)) ≅ restrictComplexSheaf X :=
  Functor.isoWhiskerLeft (sheafToPresheaf _ _)
      (sheafComposeNatIso (Opens.grothendieckTopology X)
        (ModuleCat.restrictScalars (Int.castRingHom ℂ))
        (sheafificationAdjunction _ _) (sheafificationAdjunction _ _)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (sheafificationAdjunction _ _).counit) _ ≪≫
    Functor.leftUnitor _

instance restrictComplexSheaf_preservesFiniteLimits (X : TopCat.{0}) :
    PreservesFiniteLimits (restrictComplexSheaf X) := by
  have := (complexSheafAdjunction X).isRightAdjoint
  infer_instance

instance restrictComplexSheaf_preservesFiniteColimits (X : TopCat.{0}) :
    PreservesFiniteColimits (restrictComplexSheaf X) := by
  have := (Sheaf.adjunction (Opens.grothendieckTopology X)
    (ModuleCat.restrictCoextendScalarsAdj (Int.castRingHom ℂ))).isLeftAdjoint
  exact preservesFiniteColimits_of_natIso (restrictComplexSheafIso X)

instance restrictComplexSheaf_additive (X : TopCat.{0}) :
    (restrictComplexSheaf X).Additive where
  map_add := by
    intro M N f g
    apply Sheaf.hom_ext
    ext U x
    rfl

/-- The coefficient adjunction extends to the genuine higher Ext groups. -/
def complexSheafExtAdjunction (X : TopCat.{0})
    [HasExt.{1} (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℤ))]
    [HasExt.{1} (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ))]
    (M : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℤ))
    (N : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)) (n : ℕ) :
    Abelian.Ext ((extendComplexSheaf X).obj M) N n ≃+
      Abelian.Ext M ((restrictComplexSheaf X).obj N) n :=
  ExtAdjunction.Projective.extAdjunction (restrictComplexSheaf X) M (complexSheafAdjunction X) N n

end

end OAI.AlgebraicGeometry.SheafCohomology.Coefficients.Projective
