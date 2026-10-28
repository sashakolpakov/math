import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PicardPullbackId
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineTrivializationOf
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Cube Picard Value -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubePicardValue

noncomputable section

/-! The cube class in the actual Picard group, its pullback naturality,
and cancellation on the three zero faces. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

namespace Construction.CubePicardClass

variable {K : Type u} [Field K] (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) {T T' : Over (Spec (.of K))}

def value (a : T ⟶ A) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left :=
  PicardPullbackId.Construction.PicardPullback.map a.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)

def cube (a b c : T ⟶ A) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left :=
  value A L (a * b * c) * value A L a * value A L b * value A L c /
    (value A L (a * b) * value A L (a * c) * value A L (b * c))

theorem value_one : value A L (1 : T ⟶ A) = 1 := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T.hom ≫ (MonObj.one (X := A)).left) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1
  rw [AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  have he : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (MonObj.one (X := A)).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (Spec (.of K)) :=
    Quotient.sound (LineTrivializationOf.Construction.LineTrivialization.pullback_trivial_over_field (MonObj.one (X := A)).left L)
  rw [he, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial]
  rfl

omit [GrpObj A] [IsCommMonObj A] in
theorem value_pullback (j : T' ⟶ T) (a : T ⟶ A) :
    PicardPullbackId.Construction.PicardPullback.map j.left (value A L a) = value A L (j ≫ a) := by
  exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp j.left a.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)).symm

omit [IsCommMonObj A] in
theorem pullback (j : T' ⟶ T) (a b c : T ⟶ A) :
    PicardPullbackId.Construction.PicardPullback.map j.left (cube A L a b c) = cube A L (j ≫ a) (j ≫ b) (j ≫ c) := by
  simp only [cube, map_div, map_mul, value_pullback, MonObj.comp_mul]

theorem first_one (b c : T ⟶ A) : cube A L 1 b c = 1 := by
  simp only [cube, one_mul, value_one, mul_one]
  apply div_eq_one.mpr
  ac_rfl

theorem second_one (a c : T ⟶ A) : cube A L a 1 c = 1 := by
  simp only [cube, one_mul, mul_one, value_one]
  apply div_eq_one.mpr
  ac_rfl

theorem third_one (a b : T ⟶ A) : cube A L a b 1 = 1 := by
  simp only [cube, mul_one, value_one]
  apply div_eq_one.mpr
  ac_rfl

def bundle (a b c : T ⟶ A) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle T.left := (cube A L a b c).out

omit [IsCommMonObj A] in
theorem bundle_class (a b c : T ⟶ A) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (bundle A L a b c) = cube A L a b c :=
  Quotient.out_eq _

omit [IsCommMonObj A] in
theorem bundle_trivial_of_eq (a b c : T ⟶ A) (h : cube A L a b c = 1) :
    Nonempty ((bundle A L a b c).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left) := by
  have he : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (bundle A L a b c) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial T.left) :=
    (bundle_class A L a b c).trans h
  exact Quotient.exact he

end Construction.CubePicardClass

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubePicardValue
