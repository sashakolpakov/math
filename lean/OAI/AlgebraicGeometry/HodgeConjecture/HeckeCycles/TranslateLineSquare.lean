import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GeometricCubeIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PicardPowersAdd
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine

/-! # Translate Line Square -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TranslateLineSquare.CM

noncomputable section

/-! The geometric cube identity identifies the tensor product of
opposite translates of any actual line bundle with its square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {K : Type} [Field K] [IsAlgClosed K]
  (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]

local notation "Point" => 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A

def constant (b : Point) : A ⟶ A := toUnit A ≫ b

omit [IsAlgClosed K] in
theorem constant_inverse (b : Point) : constant A b * constant A b⁻¹ = 1 := by
  change (toUnit A ≫ b) * (toUnit A ≫ b⁻¹) = 1
  rw [← MonObj.comp_mul, mul_inv_cancel, MonObj.comp_one]

omit [IsAlgClosed K] [GrpObj A] [IsCommMonObj A] in
theorem constant_class (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (b : Point) :
    Quotients.FiniteDescent.CubicalMultiplicationIs.Construction.CubicalMultiplication.pullbackClass A L (constant A b) = 1 := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.hom ≫ b.left) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1
  rw [AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  have hb : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass b.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (Spec (.of K)) :=
    Quotient.sound (Quotients.FiniteDescent.LineTrivializationOf.Construction.LineTrivialization.pullback_trivial_over_field b.left L)
  rw [hb, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial]
  rfl

theorem square_iso [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (b : Point) :
    Nonempty ((L.tensorPower 2).sheaf ≅
      ((L.pullback (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A b).hom).tensor
        (L.pullback (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A b⁻¹).hom)).sheaf) := by
  have hc := Quotients.FiniteDescent.GeometricCubeIs.Construction.GeometricCubeIdentity.isCubical A L (𝟙 A) (constant A b) (constant A b⁻¹)
  have ht : (𝟙 A : A ⟶ A) * constant A b * constant A b⁻¹ = 𝟙 A := by
    rw [mul_assoc, constant_inverse, mul_one]
  have hid : Quotients.FiniteDescent.CubicalMultiplicationIs.Construction.CubicalMultiplication.pullbackClass A L (𝟙 A) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L :=
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id _
  simp only [ht, hid, constant_class, constant_inverse,
    Quotients.FiniteDescent.CubicalMultiplicationIs.Construction.CubicalMultiplication.class_one, mul_one] at hc
  have hs : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensorPower 2) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((L.pullback (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A b).hom).tensor
        (L.pullback (Quotients.FiniteDescent.GroupAffine.Construction.GroupAffineNeighborhood.translate A b⁻¹).hom)) := by
    rw [Quotients.FiniteDescent.PicardPowersAdd.Construction.PicardPowers.class_pow, pow_two]
    exact hc
  exact Quotient.exact hs

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TranslateLineSquare.CM
