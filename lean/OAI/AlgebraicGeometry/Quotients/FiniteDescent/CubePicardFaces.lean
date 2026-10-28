import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubePicardValue
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubicalMultiplicationIs

/-! # Cube Picard Faces -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubePicardFaces.Construction.CubePicardClass

noncomputable section

/-! Vanishing of a cube class gives actual bundle frames on each zero
face, and the universal class identity yields the required cubical identity. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {K : Type u} [Field K] (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) {T T' : Over (Spec (.of K))}

omit [IsCommMonObj A] in
theorem pullback_bundle_trivial (a b c : T ⟶ A) (j : T' ⟶ T)
    (h : CubePicardValue.Construction.CubePicardClass.cube A L (j ≫ a) (j ≫ b) (j ≫ c) = 1) :
    Nonempty (((CubePicardValue.Construction.CubePicardClass.bundle A L a b c).pullback j.left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T'.left) := by
  have he : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((CubePicardValue.Construction.CubePicardClass.bundle A L a b c).pullback j.left) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial T'.left) := by
    change PicardPullbackId.Construction.PicardPullback.map j.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CubePicardValue.Construction.CubePicardClass.bundle A L a b c)) = 1
    rw [CubePicardValue.Construction.CubePicardClass.bundle_class, CubePicardValue.Construction.CubePicardClass.pullback, h]
  exact Quotient.exact he

theorem first_face (a b c : T ⟶ A) (j : T' ⟶ T) (hj : j ≫ a = 1) :
    Nonempty (((CubePicardValue.Construction.CubePicardClass.bundle A L a b c).pullback j.left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T'.left) := by
  apply pullback_bundle_trivial A L a b c j
  rw [hj, CubePicardValue.Construction.CubePicardClass.first_one]

theorem second_face (a b c : T ⟶ A) (j : T' ⟶ T) (hj : j ≫ b = 1) :
    Nonempty (((CubePicardValue.Construction.CubePicardClass.bundle A L a b c).pullback j.left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T'.left) := by
  apply pullback_bundle_trivial A L a b c j
  rw [hj, CubePicardValue.Construction.CubePicardClass.second_one]

theorem third_face (a b c : T ⟶ A) (j : T' ⟶ T) (hj : j ≫ c = 1) :
    Nonempty (((CubePicardValue.Construction.CubePicardClass.bundle A L a b c).pullback j.left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T'.left) := by
  apply pullback_bundle_trivial A L a b c j
  rw [hj, CubePicardValue.Construction.CubePicardClass.third_one]

omit [IsCommMonObj A] in
theorem eq_one_of_bundle_trivial (a b c : T ⟶ A)
    (h : Nonempty ((CubePicardValue.Construction.CubePicardClass.bundle A L a b c).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left)) :
    CubePicardValue.Construction.CubePicardClass.cube A L a b c = 1 := by
  have he : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CubePicardValue.Construction.CubePicardClass.bundle A L a b c) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial T.left) :=
    Quotient.sound h
  exact (CubePicardValue.Construction.CubePicardClass.bundle_class A L a b c).symm.trans he

omit [IsCommMonObj A] in
theorem isCubical (h : ∀ a b c : A ⟶ A, CubePicardValue.Construction.CubePicardClass.cube A L a b c = 1) : CubicalMultiplicationIs.Construction.CubicalMultiplication.IsCubical A L := by
  intro a b c
  exact div_eq_one.mp (h a b c)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubePicardFaces.Construction.CubePicardClass
