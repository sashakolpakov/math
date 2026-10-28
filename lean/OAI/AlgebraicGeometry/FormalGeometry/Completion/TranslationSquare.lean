import OAI.AlgebraicGeometry.FormalGeometry.Completion.CubeIdentity

/-! # Translation Square -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.TranslationSquare

noncomputable section

/-! Opposite translations of a line bundle tensor to its square, as a
consequence of the proved geometric cube identity. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

omit [IsAlgClosed K] [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  [GrpObj A] [IsCommMonObj A] in
theorem lineBundle_constant_class (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    {T : Over (Spec (CommRingCat.of K))} (a : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A) :
    Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.value A L (toUnit T ≫ a) = 1 := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T.hom ≫ a.left) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1
  rw [AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  have ha : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass a.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (Spec (CommRingCat.of K)) :=
    Quotient.sound (Quotients.FiniteDescent.LineTrivializationOf.Construction.LineTrivialization.pullback_trivial_over_field a.left L)
  rw [ha, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial]
  rfl

theorem opposite_translation_class (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (a : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (GrpObj.mulRight a).hom.left) *
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (GrpObj.mulRight a⁻¹).hom.left) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L ^ 2 := by
  let b : A ⟶ A := toUnit A ≫ a
  have hb : Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.value A L b = 1 := lineBundle_constant_class A L a
  have hbi : Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.value A L b⁻¹ = 1 := by
    rw [show b⁻¹ = toUnit A ≫ a⁻¹ from (GrpObj.comp_inv _ _).symm]
    exact lineBundle_constant_class A L a⁻¹
  have hid : Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.value A L (𝟙 A) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 A.left) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L
    exact AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id _
  have h := CubeIdentity.Construction.cube_class_eq_one A L (𝟙 A) b b⁻¹
  simp only [Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.cube, mul_inv_cancel_right, mul_inv_cancel,
    Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.value_one, hb, hbi, hid, mul_one] at h
  have he := (div_eq_one.mp h).symm
  have hpos : Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.value A L (𝟙 A * b) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (GrpObj.mulRight a).hom.left) := rfl
  have hneg : Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.value A L (𝟙 A * b⁻¹) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (GrpObj.mulRight a⁻¹).hom.left) := by
    rw [show b⁻¹ = toUnit A ≫ a⁻¹ from (GrpObj.comp_inv _ _).symm]
    rfl
  rw [hpos, hneg] at he
  simpa only [pow_two] using he

def oppositeTranslationSquareIso (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (a : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A) :
    ((L.pullback (GrpObj.mulRight a).hom.left).tensor
      (L.pullback (GrpObj.mulRight a⁻¹).hom.left)).sheaf ≅ (L.tensorPower 2).sheaf :=
  (Quotient.exact ((opposite_translation_class A L a).trans (Quotients.FiniteDescent.PicardPowersAdd.Construction.PicardPowers.class_pow L 2).symm)).some

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.TranslationSquare
