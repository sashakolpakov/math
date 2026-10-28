import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SheafOrdered
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCoefficient

/-! # Top Ordered -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopOrdered.Comparison

noncomputable section

/-! The actual ordered top-form comparison induces the original
bounded crystalline top edge, with its unchanged total-complex sign. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))
  (g : ℕ) [SmoothOfRelativeDimension g X.hom]

def map := TopCoefficient.map p k n X g ≫
  SheafProduct.OrderedComparison.orderedMap p k n X Y f hp I

theorem comparison (x : IntrinsicDeRham.TopEdge.Intrinsic.source (Truncated.Witt.Ring p k n) X
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) g) :
    homologyMap (Comparison.map p k n X Y f hp I g) (g+g)
      (TopCoefficient.sourceInput p k n X g x) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g •
      CechIso.ResolutionGlobal.toOrdered p k n X Y f I
        (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) (g+g)
        (IntrinsicCohomology.Intrinsic.comparisonEquiv p k n X Y f hp I (g+g)
          (IntrinsicDeRham.TopEdge.Intrinsic.map (Truncated.Witt.Ring p k n) X
            (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) g x)) := by
  rw [Comparison.map, homologyMap_comp, ConcreteCategory.comp_apply,
    TopCoefficient.comparison]
  simp only [Units.smul_def, map_zsmul]
  exact congrArg (fun y => ((ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g : ℤˣ) : ℤ) • y)
    (SheafOrdered.Comparison.ordered_apply p k n X Y f hp I (g+g)
      (IntrinsicDeRham.TopEdge.Intrinsic.map (Truncated.Witt.Ring p k n) X
        (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) g x))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopOrdered.Comparison
