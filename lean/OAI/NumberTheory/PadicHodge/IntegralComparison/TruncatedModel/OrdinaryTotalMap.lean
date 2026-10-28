import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryAssemblyCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TotalFunctorMap

/-! # Ordinary Total Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryTotalMap.Ordinary

noncomputable section

/-! The genuine ordinary section map factors under the actual total
functor. The original frame-comparison presentation is identified in
a separate equality. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
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

abbrev totalFunctor := OrdinaryAssemblyCoordinates.Ordinary.affineTotalFunctor p k n X

omit [Fintype k] [CharP k p] in
private theorem total_map
    {C₁ C₂ : CochainComplex (X.left.affineOpensᵒᵖ ⥤
      ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ}
    (a : C₁ ⟶ C₂) :
    (totalFunctor p k n X).map a = AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map.{1,2}
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
      (NonemptyCechNerve.nerve (CechSliceResolution.opens p k n X)) a :=
  Cech.TotalFunctorMap.map.{1,2}
    (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
    (NonemptyCechNerve.nerve (CechSliceResolution.opens p k n X)) a

def frameMap : (totalFunctor p k n X).obj (OrdinarySectionMap.Ordinary.source p k n X) ⟶
    FrameCech.Complexes.source p k n X Y f hp :=
  (totalFunctor p k n X).map (OrdinarySectionMap.Ordinary.frameIso p k n X Y f hp).inv

def resolutionMap : FrameCech.Complexes.source p k n X Y f hp ⟶
    FrameCech.Complexes.target p k n X Y f I :=
  (totalFunctor p k n X).map (FrameInjective.Comparison.map p k n X Y f hp I)

def map : (totalFunctor p k n X).obj (OrdinarySectionMap.Ordinary.source p k n X) ⟶
    FrameCech.Complexes.target p k n X Y f I :=
  (totalFunctor p k n X).map (OrdinarySectionMap.Ordinary.map p k n X Y f hp I)

theorem factorization : Ordinary.map p k n X Y f hp I =
    frameMap p k n X Y f hp ≫ resolutionMap p k n X Y f hp I :=
  (totalFunctor p k n X).map_comp
    (OrdinarySectionMap.Ordinary.frameIso p k n X Y f hp).inv
    (FrameInjective.Comparison.map p k n X Y f hp I)

theorem resolutionMap_eq : resolutionMap p k n X Y f hp I =
    FrameCech.Comparison.map p k n X Y f hp I :=
  total_map p k n X (FrameInjective.Comparison.map p k n X Y f hp I)

theorem comparison : Ordinary.map p k n X Y f hp I =
    frameMap p k n X Y f hp ≫ FrameCech.Comparison.map p k n X Y f hp I := by
  rw [factorization, resolutionMap_eq]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryTotalMap.Ordinary
