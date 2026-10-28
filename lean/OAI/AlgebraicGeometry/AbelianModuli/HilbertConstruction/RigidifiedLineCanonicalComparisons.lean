import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RigidifiedLineSquarePullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RigidifiedGlobalFunctions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PicardFunctions
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FieldBaseChangeConstants

/-! # Rigidified Line Canonical Comparisons -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Existing line isomorphisms have a unique representative preserving
the actual zero frames. Their identity, composition, and restriction
compatibilities follow from uniqueness, including over nonreduced tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory
universe u

section
variable {X S : Scheme.{u}} {x : S ⟶ X}

def RigidifiedLineBundles.RigidifiedLineBundle.comparison (hx : Function.Bijective x.appTop) (L M : RigidifiedLineBundles.RigidifiedLineBundle x)
    (h : Nonempty (L.lineBundle.sheaf ≅ M.lineBundle.sheaf)) : RigidifiedLineBundles.RigidifiedLineBundleIso L M :=
  Classical.choice ((RigidifiedGlobalFunctions.rigidifiedBundleIso_nonempty_iff_of_globalFunctions x hx L M).mpr h)

theorem RigidifiedLineBundles.RigidifiedLineBundle.comparison_self (hx : Function.Bijective x.appTop) (L : RigidifiedLineBundles.RigidifiedLineBundle x)
    (h : Nonempty (L.lineBundle.sheaf ≅ L.lineBundle.sheaf)) :
    RigidifiedLineBundles.RigidifiedLineBundle.comparison hx L L h = RigidifiedLineBundles.RigidifiedLineBundleIso.refl L := by
  let := RigidifiedGlobalFunctions.rigidifiedBundleIso_subsingleton_of_globalFunctions x hx.1 L L
  exact Subsingleton.elim _ _

theorem RigidifiedLineBundles.RigidifiedLineBundle.comparison_comp (hx : Function.Bijective x.appTop) (L M N : RigidifiedLineBundles.RigidifiedLineBundle x)
    (hLM : Nonempty (L.lineBundle.sheaf ≅ M.lineBundle.sheaf))
    (hMN : Nonempty (M.lineBundle.sheaf ≅ N.lineBundle.sheaf))
    (hLN : Nonempty (L.lineBundle.sheaf ≅ N.lineBundle.sheaf)) :
    (RigidifiedLineBundles.RigidifiedLineBundle.comparison hx L M hLM).trans (RigidifiedLineBundles.RigidifiedLineBundle.comparison hx M N hMN) = RigidifiedLineBundles.RigidifiedLineBundle.comparison hx L N hLN := by
  let := RigidifiedGlobalFunctions.rigidifiedBundleIso_subsingleton_of_globalFunctions x hx.1 L N
  exact Subsingleton.elim _ _

theorem RigidifiedLineBundles.RigidifiedLineBundle.comparison_pullbackSquare {Y T : Scheme.{u}}
    (hx : Function.Bijective x.appTop) (L M : RigidifiedLineBundles.RigidifiedLineBundle x)
    (hLM : Nonempty (L.lineBundle.sheaf ≅ M.lineBundle.sheaf))
    (f : Y ⟶ X) (y : T ⟶ Y) (a : T ⟶ S) (h : y ≫ f = a ≫ x)
    (hy : Function.Bijective y.appTop)
    (hLM' : Nonempty ((L.pullbackSquare f y a h).lineBundle.sheaf ≅
      (M.pullbackSquare f y a h).lineBundle.sheaf)) :
    (RigidifiedLineBundles.RigidifiedLineBundle.comparison hx L M hLM).pullbackSquare f y a h =
      RigidifiedLineBundles.RigidifiedLineBundle.comparison hy (L.pullbackSquare f y a h) (M.pullbackSquare f y a h) hLM' := by
  let := RigidifiedGlobalFunctions.rigidifiedBundleIso_subsingleton_of_globalFunctions y hy.1
    (L.pullbackSquare f y a h) (M.pullbackSquare f y a h)
  exact Subsingleton.elim _ _

end

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization
variable {S : Scheme.{0}} [IsLocallyNoetherian S] {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

theorem Abelian.Schemes.AbelianScheme.familyZero_globalFunctions_bijective (T : Over S) :
    Function.Bijective (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left.appTop := by
  let : IsIso (fst T A.scheme).left.appTop :=
    ReferenceFamily.Relative.PicardFunctions.RelativePicardFunctions.isIso_product_app A T ⊤
  let : IsIso (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left.appTop :=
    Proper.FieldBaseChangeConstants.section_globalFunctions_isIso (fst T A.scheme).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left
      (Isogenies.NeighborCounting.PoincareNormalization.familyZero_projection A T)
  exact ConcreteCategory.bijective_of_isIso _

/-- Canonical normalized comparison for any two independently specified
line objects on a test family of a locally Noetherian abelian scheme. -/
def Abelian.Schemes.AbelianScheme.rigidifiedProductComparison (T : Over S)
    (L M : RigidifiedLineBundles.RigidifiedLineBundle (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left)
    (h : Nonempty (L.lineBundle.sheaf ≅ M.lineBundle.sheaf)) : RigidifiedLineBundles.RigidifiedLineBundleIso L M :=
  RigidifiedLineBundles.RigidifiedLineBundle.comparison (A.familyZero_globalFunctions_bijective T) L M h

theorem Abelian.Schemes.AbelianScheme.rigidifiedProductComparison_comp (T : Over S)
    (L M N : RigidifiedLineBundles.RigidifiedLineBundle (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left)
    (hLM : Nonempty (L.lineBundle.sheaf ≅ M.lineBundle.sheaf))
    (hMN : Nonempty (M.lineBundle.sheaf ≅ N.lineBundle.sheaf))
    (hLN : Nonempty (L.lineBundle.sheaf ≅ N.lineBundle.sheaf)) :
    (A.rigidifiedProductComparison T L M hLM).trans (A.rigidifiedProductComparison T M N hMN) =
      A.rigidifiedProductComparison T L N hLN :=
  RigidifiedLineBundles.RigidifiedLineBundle.comparison_comp (A.familyZero_globalFunctions_bijective T) L M N hLM hMN hLN

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
