import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.CechBicomplex
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Adjunction -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.Adjunction.CrystallineZariskiAdjunction

noncomputable section

/-!
# The exact inverse image adjoint to the native Zariski direct image

Precomposition followed by sheafification gives the inverse image.
The original right Kan direct image is its right adjoint. Exactness
of inverse image therefore makes the direct image preserve injectives.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "Z" => Opens.grothendieckTopology X.left

abbrev precomposition : (X.left.Opensᵒᵖ ⥤ V) ⥤ ((Site.Object p k X)ᵒᵖ ⥤ V) :=
  (Functor.whiskeringLeft _ _ V).obj (ResidualCover.CrystallineResidualCover.functor p k X).op

def pullback : Sheaf Z V ⥤ Sheaf J V :=
  sheafToPresheaf Z V ⋙ precomposition p k X ⋙ presheafToSheaf J V

def adjunction : pullback p k X ⊣ Image.CrystallineZariskiImage.functor p k X :=
  (((ResidualCover.CrystallineResidualCover.functor p k X).op.ranAdjunction V).comp
    (sheafificationAdjunction J V)).restrictFullyFaithful
      (fullyFaithfulSheafToPresheaf Z V) (Functor.FullyFaithful.id (Sheaf J V))
      (Functor.rightUnitor (pullback p k X)).symm
      ((Functor.leftUnitor _).trans
        ((ResidualCover.CrystallineResidualCover.functor p k X).sheafPushforwardCocontinuousCompSheafToPresheafIso
          V J Z).symm)

instance pullback_finiteLimits : PreservesFiniteLimits (pullback p k X) := by
  have : PreservesFiniteLimits (precomposition p k X ⋙ presheafToSheaf J V) :=
    comp_preservesFiniteLimits _ _
  exact comp_preservesFiniteLimits _ _

instance pullback_leftAdjoint : (pullback p k X).IsLeftAdjoint := (adjunction p k X).isLeftAdjoint

instance directImage_rightAdjoint : (Image.CrystallineZariskiImage.functor p k X).IsRightAdjoint :=
  (adjunction p k X).isRightAdjoint

instance directImage_preservesInjectives :
    (Image.CrystallineZariskiImage.functor p k X).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (adjunction p k X)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.Adjunction.CrystallineZariskiAdjunction
