import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.AssociatorGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorBaseChange

/-! # Class Monoid -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Tensor product makes line-bundle isomorphism classes a commutative monoid, functorial under every base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

theorem Line.Bundles.LineBundle.tensorClass_assoc (a b c : Line.Bundles.LineBundle.IsoClass X) :
    Line.Bundles.LineBundle.tensorClass (Line.Bundles.LineBundle.tensorClass a b) c = Line.Bundles.LineBundle.tensorClass a (Line.Bundles.LineBundle.tensorClass b c) := by
  induction a using Quotient.inductionOn with
  | h L =>
    induction b using Quotient.inductionOn with
    | h M =>
      induction c using Quotient.inductionOn with
      | h N => exact Quotient.sound ⟨L.tensorAssocIso M N⟩

instance Line.Bundles.LineBundle.isoClassCommMonoid (X : Scheme.{u}) : CommMonoid (Line.Bundles.LineBundle.IsoClass X) where
  mul := Line.Bundles.LineBundle.tensorClass
  one := Line.Bundles.LineBundle.trivialClass X
  mul_assoc := Line.Bundles.LineBundle.tensorClass_assoc
  one_mul := Line.Bundles.LineBundle.tensorClass_trivial_left
  mul_one := Line.Bundles.LineBundle.tensorClass_trivial_right
  mul_comm := Line.Bundles.LineBundle.tensorClass_comm

@[simp]
theorem Line.Bundles.LineBundle.classOf_tensor (L M : Line.Bundles.LineBundle X) : Line.Bundles.LineBundle.classOf (L.tensor M) = Line.Bundles.LineBundle.classOf L * Line.Bundles.LineBundle.classOf M := rfl

@[simp]
theorem Line.Bundles.LineBundle.classOf_trivial (X : Scheme.{u}) : Line.Bundles.LineBundle.classOf (Line.Bundles.LineBundle.trivial X) = 1 := rfl

theorem Line.Bundles.LineBundle.pullbackClass_mul (f : X ⟶ Y) (a b : Line.Bundles.LineBundle.IsoClass Y) :
    Line.Bundles.LineBundle.pullbackClass f (a * b) = Line.Bundles.LineBundle.pullbackClass f a * Line.Bundles.LineBundle.pullbackClass f b := by
  induction a using Quotient.inductionOn with
  | h L =>
    induction b using Quotient.inductionOn with
    | h M => exact Quotient.sound ⟨Line.Bundles.LineBundle.tensorBaseChangeIso f L M⟩

def Line.Bundles.LineBundle.pullbackClassMonoidHom (f : X ⟶ Y) : Line.Bundles.LineBundle.IsoClass Y →* Line.Bundles.LineBundle.IsoClass X where
  toFun := Line.Bundles.LineBundle.pullbackClass f
  map_one' := Line.Bundles.LineBundle.pullbackClass_trivial f
  map_mul' := Line.Bundles.LineBundle.pullbackClass_mul f

@[simp]
theorem Line.Bundles.LineBundle.pullbackClassMonoidHom_id : Line.Bundles.LineBundle.pullbackClassMonoidHom (𝟙 X) = MonoidHom.id (Line.Bundles.LineBundle.IsoClass X) := by
  ext q
  exact Line.Bundles.LineBundle.pullbackClass_id q

theorem Line.Bundles.LineBundle.pullbackClassMonoidHom_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    Line.Bundles.LineBundle.pullbackClassMonoidHom (f ≫ g) = (Line.Bundles.LineBundle.pullbackClassMonoidHom f).comp (Line.Bundles.LineBundle.pullbackClassMonoidHom g) := by
  ext q
  exact Line.Bundles.LineBundle.pullbackClass_comp f g q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
