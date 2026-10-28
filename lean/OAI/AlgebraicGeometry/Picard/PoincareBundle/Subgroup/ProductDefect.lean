import OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationDefect

/-! # Product Defect -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.ProductDefect

noncomputable section

/-! The regular defect attached to two elements of a commutative subgroup scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationFibers
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationDefect

variable {S : Scheme.{u}} {H A : Over S} [GrpObj H] [IsCommMonObj H] [GrpObj A]
  (i : H ⟶ A) [IsMonHom i] (L : Line.Bundles.LineBundle A.left)
  (t : Line.Fibers.fiber L (snd H A) ≅ Line.Fibers.fiber L (NormalizedKernelTranslation.action i))

theorem translate_mul {T : Over S} (a b : T ⟶ H) (x : T ⟶ A) :
    (b ≫ i) * ((a ≫ i) * x) = ((a * b) ≫ i) * x := by
  calc
    (b ≫ i) * ((a ≫ i) * x) = ((b * a) ≫ i) * x := by rw [MonObj.mul_comp, mul_assoc]
    _ = ((a * b) ≫ i) * x := congrArg (fun c => (c ≫ i) * x) (mul_comm b a)

/-- The defect is computed from actual transport at the starting point and its two translates. -/
def value {T : Over S} (a b : T ⟶ H) (x : T ⟶ A) : Γ(T.left, ⊤)ˣ :=
  TranslationDefect.defect i L t x ((a ≫ i) * x) (((a * b) ≫ i) * x) a b (a * b)
    rfl (translate_mul i a b x) rfl

omit [GrpObj H] [IsCommMonObj H] [IsMonHom i] in
theorem translated_point_natural {T U : Over S} (g : U ⟶ T) (a : T ⟶ H) (x : T ⟶ A) :
    g ≫ ((a ≫ i) * x) = ((g ≫ a) ≫ i) * (g ≫ x) := by
  rw [MonObj.comp_mul, ← Category.assoc]

theorem value_natural {T U : Over S} (g : U ⟶ T) (a b : T ⟶ H) (x : T ⟶ A) :
    value i L t (g ≫ a) (g ≫ b) (g ≫ x) = Units.map g.left.appTop.hom (value i L t a b x) := by
  apply TranslationDefect.defect_natural i L t g x ((a ≫ i) * x) (((a * b) ≫ i) * x) a b (a * b)
    rfl (translate_mul i a b x) rfl
    (g ≫ x) (((g ≫ a) ≫ i) * (g ≫ x))
    ((((g ≫ a) * (g ≫ b)) ≫ i) * (g ≫ x)) (g ≫ a) (g ≫ b) ((g ≫ a) * (g ≫ b))
    rfl (translate_mul i (g ≫ a) (g ≫ b) (g ≫ x)) rfl
  · rfl
  · exact translated_point_natural i g a x
  · exact (translated_point_natural i g (a * b) x).trans
      (congrArg (fun c => (c ≫ i) * (g ≫ x)) (MonObj.comp_mul g a b))
  · rfl
  · rfl
  · exact MonObj.comp_mul g a b

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.ProductDefect
