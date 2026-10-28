import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.AlgebraicGeometry.Scheme

/-! # Test Scheme Lift -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TestSchemeLift

/-! Every test over a base-changed parameter scheme is canonically a test over the changed base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S S' : Scheme.{u}} (s : S' ⟶ S) (T : Over S') (U : Over S)
  (a : U ⟶ (Over.map s).obj T)

/-- The map to the parameter supplies the changed-base structure on the test. -/
def object : Over S' := Over.mk (a.left ≫ T.hom)

/-- Forgetting the newly supplied base structure recovers the original test scheme. -/
def iso : (Over.map s).obj (object s T U a) ≅ U :=
  Over.isoMk (Iso.refl U.left) ((Category.id_comp U.hom).trans
    (a.w.symm.trans (Category.assoc a.left T.hom s).symm))

/-- The original map to the parameter is now a morphism over the changed base. -/
def map : object s T U a ⟶ T := Over.homMk a.left rfl

/-- The original and changed-base parameter maps agree as actual scheme maps. -/
theorem map_eq : (Over.map s).map (TestSchemeLift.map s T U a) = (iso s T U a).hom ≫ a :=
  Over.OverMorphism.ext (Category.id_comp a.left).symm

/-- This comparison changes no underlying scheme coordinates. -/
theorem iso_left : (iso s T U a).hom.left = 𝟙 U.left := rfl

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TestSchemeLift
