import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryTotalMap

/-! # Ordinary Global -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryGlobal.OrdinaryComparison

noncomputable section

/-! The original global de Rham comparison is induced by the actual
affine ordinary-section map, after its canonical coefficient coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

abbrev totalFunctor : CochainComplex (X.left.affineOpensᵒᵖ ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ ⥤
      CochainComplex (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ :=
  OrdinaryAssemblyCoordinates.Ordinary.affineTotalFunctor p k n X

def coordinates : GlobalDeRham.Comparison.complex p k n X ≅
    (totalFunctor p k n X).obj (OrdinarySectionMap.Ordinary.source p k n X) :=
  OrdinaryAssemblyCoordinates.Ordinary.sourceIso p k n X

omit [IsSeparated Y.hom] in
theorem coordinate_frame :
    (coordinates p k n X).hom ≫
      (totalFunctor p k n X).map (OrdinarySectionMap.Ordinary.frameIso p k n X Y f hp).inv =
    (GlobalDeRham.Comparison.iso p k n X Y f hp).hom :=
  OrdinaryAssemblyCoordinates.Ordinary.comparison p k n X Y f hp

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

def map : (totalFunctor p k n X).obj (OrdinarySectionMap.Ordinary.source p k n X) ⟶
    FrameCech.Complexes.target p k n X Y f I :=
  (totalFunctor p k n X).map (OrdinarySectionMap.Ordinary.map p k n X Y f hp I)

theorem map_factorization : OrdinaryComparison.map p k n X Y f hp I =
    (totalFunctor p k n X).map (OrdinarySectionMap.Ordinary.frameIso p k n X Y f hp).inv ≫
      FrameCech.Comparison.map p k n X Y f hp I :=
  OrdinaryTotalMap.Ordinary.comparison p k n X Y f hp I

theorem comparison :
    (coordinates p k n X).hom ≫ OrdinaryComparison.map p k n X Y f hp I =
      (GlobalDeRham.Comparison.iso p k n X Y f hp).hom ≫
        FrameCech.Comparison.map p k n X Y f hp I := by
  rw [map_factorization, ← Category.assoc, coordinate_frame]

def toBounded (q : ℕ) :=
  homologyMap (OrdinaryComparison.map p k n X Y f hp I) q ≫
    (GlobalEdge.InjectiveCech.homologyIso p k n X Y f I q).hom

theorem homology_comparison (q : ℕ) :
    homologyMap (coordinates p k n X).hom q ≫ toBounded p k n X Y f hp I q =
      (GlobalDeRham.Comparison.homologyIso p k n X Y f hp I q).hom := by
  unfold toBounded
  rw [← Category.assoc, ← homologyMap_comp, comparison, homologyMap_comp]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryGlobal.OrdinaryComparison
