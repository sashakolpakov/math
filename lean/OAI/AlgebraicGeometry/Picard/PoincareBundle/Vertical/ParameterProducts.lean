import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ParameterKernelFrames

/-! # Parameter Products -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ParameterProducts

noncomputable section

/-! The parameter family's genuine product is the original bilinear map through the actual fiber comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ParameterKernelFrames

/-- Equal coordinate presentations retain the actual bilinear product. -/
theorem congrCoordinates_product {S : Scheme.{u}} {E A X : Over S} [GrpObj A]
    {p p' : E ⟶ A} {r r' : E ⟶ X} (L : Line.Bundles.LineBundle E.left)
    (D : FiberwiseMultiplication.Multiplication p r L) (hp : p = p') (hr : r = r')
    {T : Over S} (a b c : T ⟶ E) (h : FiberwiseMultiplication.ProductRel p r a b c) (h' : FiberwiseMultiplication.ProductRel p' r' a b c) :
    (MultiplicationCoordinates.congrCoordinates D hp hr).product a b c h' = D.product a b c h := by
  cases hp
  cases hr
  rfl

variable {S : Scheme.{u}} {K A X : Over S} [GrpObj X]
  (t : K ⟶ A) (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)

/-- The actual vertical relation maps to the original family relation under arbitrary parameter change. -/
theorem mapped_relation {T : Over S} (a b c : T ⟶ K ⊗ X)
    (h : FiberwiseMultiplication.ProductRel (snd K X) (fst K X) a b c) :
    FiberwiseMultiplication.ProductRel (snd A X) (fst A X) (a ≫ (t ⊗ₘ 𝟙 X)) (b ≫ (t ⊗ₘ 𝟙 X)) (c ≫ (t ⊗ₘ 𝟙 X)) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Category.assoc, tensorHom_snd, Category.comp_id] using h.1
  · simpa only [Category.assoc, tensorHom_fst] using congrArg (fun z => z ≫ t) h.2.1
  · simpa only [Category.assoc, tensorHom_fst] using congrArg (fun z => z ≫ t) h.2.2

/-- No abstract class comparison enters the parameter product: its entire bilinear sheaf map is the actual transported product. -/
theorem product_eq {T : Over S} (a b c : T ⟶ K ⊗ X)
    (h : FiberwiseMultiplication.ProductRel (snd K X) (fst K X) a b c) :
    (ParameterKernelFrames.multiplication t L Dv).product a b c h =
    Pulled.LineBilinear.transport (t ⊗ₘ 𝟙 X) L a b c
      (a ≫ (t ⊗ₘ 𝟙 X)) (b ≫ (t ⊗ₘ 𝟙 X)) (c ≫ (t ⊗ₘ 𝟙 X)) rfl rfl rfl
      (Dv.product _ _ _ (mapped_relation t a b c h)) := by
  have hr : FiberwiseMultiplication.ProductRel ((t ⊗ₘ 𝟙 X) ≫ snd A X) ((t ⊗ₘ 𝟙 X) ≫ fst A X) a b c := by
    simpa only [FiberwiseMultiplication.ProductRel, Category.assoc] using mapped_relation t a b c h
  unfold ParameterKernelFrames.multiplication MultiplicationFixedMap.restrictFixed
  dsimp only
  unfold ParameterKernelFrames.imageMultiplication
  rw [congrCoordinates_product (L.pullback (t ⊗ₘ 𝟙 X).left)
    (FiberwiseMultiplicationPullback.pullbackMultiplication (snd A X) (fst A X) (t ⊗ₘ 𝟙 X) L Dv) (by simp) (by simp) a b c hr]
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ParameterProducts
