import OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.NeutralProductComparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.OriginTranslationRatio

/-! # Origin Ratios -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.OriginRatios

noncomputable section

/-! Identify actual origin translation ratios with the constructed neutral-row automorphism coefficient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

section

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionFrames
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.IsoRatios OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.AutomorphismUnits OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberIsomorphismRatios OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationFibers

variable {S : Scheme.{u}} {H A : Over S} [GrpObj H] [GrpObj A] (i : H ⟶ A) [IsMonHom i]
  (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (L : Line.Bundles.LineBundle A.left)
  (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (Line.Fibers.fiber L (fst A A))) (Line.Fibers.fiber L (snd A A)) ≅ Line.Fibers.fiber L μ[A])
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ A).left ≅ (Scheme.Modules.pullback (i ⊗ₘ 𝟙 A).left).obj Q.sheaf)
  (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (A ⊗ H).left ≅ (Scheme.Modules.pullback (𝟙 A ⊗ₘ i).left).obj Q.sheaf)
  (u : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule H.left ≅ Line.Fibers.fiber L i)
  (o : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (𝟙_ (Over S)).left ≅ Line.Fibers.fiber L η[A])

def originRatio {T : Over S} (a : T ⟶ H) : Γ(T.left, ⊤)ˣ :=
  Line.IsoRatios.ratio (FiberIsomorphismRatios.fiberLine L (1 : T ⟶ A))
    (Subgroup.TranslationFibers.transportIso i L (FramedSubgroupInducingProduct.translationIso i Q L e s u)
      (1 : T ⟶ A) (a ≫ i) a (mul_one (a ≫ i)))
    ((NaturalOriginLineFrames.frame L o T).symm ≪≫ GlobalPullbackFrame.atPoint i L u a (a ≫ i) rfl)

/-- The origin ratio is the coefficient of an actual automorphism defined along the full neutral row. -/
theorem originRatio_eq
    (hi : ∀ (T : Over S) (a b : T ⟶ H), Kernel.IntersectionFrames.obstruction i i (Line.Comparison.Bundle.fromShared Q) s t a b = 1)
    {T : Over S} (a : T ⟶ H) :
    originRatio i Q L e s u o a = Line.AutomorphismUnits.unitOfAut (FiberIsomorphismRatios.fiberLine L (a ≫ i))
      (ProperFiberAutomorphismScalar.atPoint L
        (Neutral.RowInducingAutomorphism.automorphism Q L e (Kernel.NeutralRowFrame.frame i (Line.Comparison.Bundle.fromShared Q) t)
          (NaturalOriginLineFrames.frame L o A)) (a ≫ i)) := by
  have hβ := NeutralProductComparison.origin_product i Q L e s t hi a
  have hc := Neutral.RowContractionFormula.atPoint_hom Q L e
    (Kernel.NeutralRowFrame.frame i (Line.Comparison.Bundle.fromShared Q) t) o (a ≫ i)
  apply OriginTranslationRatio.ratio_eq (FiberIsomorphismRatios.fiberLine L (1 : T ⟶ A)) (FiberIsomorphismRatios.fiberLine L (a ≫ i))
    (FramedSubgroupFiberProducts.atPoint i Q L e s a (1 : T ⟶ A) (a ≫ i) (mul_one (a ≫ i)))
    (GlobalPullbackFrame.atPoint i L u a (a ≫ i) rfl) (NaturalOriginLineFrames.frame L o T)
    (Subgroup.TranslationFibers.transportIso i L (FramedSubgroupInducingProduct.translationIso i Q L e s u)
      (1 : T ⟶ A) (a ≫ i) a (mul_one (a ≫ i)))
    (ProperFiberAutomorphismScalar.atPoint L
      (Neutral.RowInducingAutomorphism.automorphism Q L e (Kernel.NeutralRowFrame.frame i (Line.Comparison.Bundle.fromShared Q) t)
        (NaturalOriginLineFrames.frame L o A)) (a ≫ i))
  · exact FramedSubgroupFiberProducts.transport_contraction i Q L e s u a (1 : T ⟶ A) (a ≫ i) (mul_one (a ≫ i))
  · exact hc.trans (congrArg (fun b => AbelianScheme.IsogenyQuotient.RightContraction.Construction.lineContractRight b (NaturalOriginLineFrames.frame L o T).hom) hβ).symm

end

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionFrames

variable {k : Type u} [Field k] {H A : Over (Spec (.of k))} [GrpObj H] [GrpObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom] (i : H ⟶ A) [IsMonHom i]
  (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (L : Line.Bundles.LineBundle A.left)
  (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (Line.Fibers.fiber L (fst A A))) (Line.Fibers.fiber L (snd A A)) ≅ Line.Fibers.fiber L μ[A])
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (H ⊗ A).left ≅ (Scheme.Modules.pullback (i ⊗ₘ 𝟙 A).left).obj Q.sheaf)
  (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (A ⊗ H).left ≅ (Scheme.Modules.pullback (𝟙 A ⊗ₘ i).left).obj Q.sheaf)
  (u : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule H.left ≅ Line.Fibers.fiber L i)
  (o : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (𝟙_ (Over (Spec (.of k)))).left ≅ Line.Fibers.fiber L η[A])

/-- Isotropy and proper group geometry force equal origin ratios on every test scheme. -/
theorem originRatio_uniform
    (hi : ∀ (T : Over (Spec (.of k))) (a b : T ⟶ H), Kernel.IntersectionFrames.obstruction i i (Line.Comparison.Bundle.fromShared Q) s t a b = 1)
    {T : Over (Spec (.of k))} (a b : T ⟶ H) :
    originRatio i Q L e s u o a = originRatio i Q L e s u o b :=
  (originRatio_eq i Q L e s t u o hi a).trans
    ((Neutral.RowInducingAutomorphism.uniform_coefficient A Q L e (Kernel.NeutralRowFrame.frame i (Line.Comparison.Bundle.fromShared Q) t)
      o (a ≫ i) (b ≫ i)).trans (originRatio_eq i Q L e s t u o hi b).symm)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.OriginRatios
