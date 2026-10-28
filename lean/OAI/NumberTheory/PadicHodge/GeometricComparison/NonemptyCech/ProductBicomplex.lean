import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBaseChangeNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits

/-! # Product Bicomplex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex

noncomputable section

/-! The tuple-product base-change isomorphism applies to original Cech bicomplexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v s t a b w
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type s} [Category.{t} D] [Quiver.IsThin D] [HasBinaryProducts D]
  {A : Type a} [Category.{b} A] [Preadditive A] [HasProducts.{w} A]
  (F : C ⥤ D) {ι : Type w} (U : ι → C)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]

def pullback : (Dᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A) := (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op

instance pullback_additive : (pullback (A := A) F).Additive := by
  dsimp only [pullback]
  infer_instance

instance source_additive : (IntegralComparison.NonemptyCechNerve.complexFunctor (A := A) U).Additive := by
  change (FormalCoproduct.cochainComplexFunctor (IntegralComparison.NonemptyCechNerve.nerve U)).Additive
  infer_instance

instance target_additive : (IntegralComparison.NonemptyCechNerve.complexFunctor (A := A) (F.obj ∘ U)).Additive := by
  change (FormalCoproduct.cochainComplexFunctor (IntegralComparison.NonemptyCechNerve.nerve (F.obj ∘ U))).Additive
  infer_instance

variable (K : CochainComplex (Dᵒᵖ ⥤ A) ℕ)

def iso :
    ((IntegralComparison.NonemptyCechNerve.complexFunctor U).mapHomologicalComplex (.up ℕ)).obj
      (((pullback F).mapHomologicalComplex (.up ℕ)).obj K) ≅
    ((IntegralComparison.NonemptyCechNerve.complexFunctor (F.obj ∘ U)).mapHomologicalComplex (.up ℕ)).obj K :=
  (NatIso.mapHomologicalComplex (ProductBaseChangeNaturality.NonemptyCechProductBaseChangeNaturality.iso F U)
    (.up ℕ)).app K

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex
