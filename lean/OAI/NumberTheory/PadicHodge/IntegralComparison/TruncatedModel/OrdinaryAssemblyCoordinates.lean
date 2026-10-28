import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinarySectionMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.AssemblyInverseCoordinates

/-! # Ordinary Assembly Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryAssemblyCoordinates.Ordinary

noncomputable section

/-! The native ordinary comparison has the canonical assembled
coefficient square. The two native presentations of its right map and
output coordinates are identified separately. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

abbrev sourceIso :=
  ((Principal.Comparison.coefficients p k).mapHomologicalComplex (.up ℕ)).mapIso
    (OrdinaryCechCoordinates.Ordinary.iso p k n X) ≪≫
    GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso (Principal.Comparison.coefficients p k)
      (NonemptyCechNerve.nerve (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (Truncated.Witt.Ring p k n) X))
      (Small.OrdinaryCechTotal.Ordinary.finiteIndices (Truncated.Witt.Ring p k n) X)
      (OrdinaryBaseIso.Ordinary.target p k n X)

abbrev frameMap :=
  (GeometricComparison.CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor
    (NonemptyCechNerve.nerve (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (Truncated.Witt.Ring p k n) X))).map
      (Functor.isoWhiskerRight (OrdinaryBaseIso.Ordinary.pdIso p k n X Y f hp)
        ((Principal.Comparison.coefficients p k).mapHomologicalComplex (.up ℕ))).inv

abbrev targetIso :=
  ((Principal.Comparison.coefficients p k).mapHomologicalComplex (.up ℕ)).mapIso
    (OrdinaryCechCoordinates.Ordinary.iso p k n X ≪≫
      GeometricComparison.CechAssembly.Iso.CechAssemblyIso.totalIso
        (NonemptyCechNerve.nerve (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (Truncated.Witt.Ring p k n) X))
        (OrdinaryBaseIso.Ordinary.pdIso p k n X Y f hp).symm) ≪≫
    GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso (Principal.Comparison.coefficients p k)
      (NonemptyCechNerve.nerve (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (Truncated.Witt.Ring p k n) X))
      (Small.OrdinaryCechTotal.Ordinary.finiteIndices (Truncated.Witt.Ring p k n) X)
      (PrincipalComplex.Comparison.pdComplexes p k n X Y f hp)

omit [IsSeparated Y.hom] in
theorem square : (sourceIso p k n X).hom ≫ frameMap p k n X Y f hp =
    (targetIso p k n X Y f hp).hom :=
  Cech.AssemblyInverseCoordinates.coordinates
    (Principal.Comparison.coefficients p k)
    (NonemptyCechNerve.nerve (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (Truncated.Witt.Ring p k n) X))
    (Small.OrdinaryCechTotal.Ordinary.finiteIndices (Truncated.Witt.Ring p k n) X)
    (OrdinaryBaseIso.Ordinary.pdIso p k n X Y f hp)
    (OrdinaryCechCoordinates.Ordinary.iso p k n X)

omit [IsSeparated Y.hom] in
theorem targetIso_eq : targetIso p k n X Y f hp =
    GlobalDeRham.Comparison.iso p k n X Y f hp := rfl

abbrev affineTotalFunctor : CochainComplex (X.left.affineOpensᵒᵖ ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ ⥤
      CochainComplex (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ :=
  FrameCech.Complexes.cechFunctor p k n X ⋙
    HomologicalComplex₂.totalFunctor _ (.up ℕ) (.up ℕ) (.up ℕ)

omit [IsSeparated Y.hom] in
theorem frameMap_eq : frameMap p k n X Y f hp =
    (affineTotalFunctor p k n X).map
      (OrdinarySectionMap.Ordinary.frameIso p k n X Y f hp).inv := rfl

omit [IsSeparated Y.hom] in
theorem comparison : (sourceIso p k n X).hom ≫
    (affineTotalFunctor p k n X).map
      (OrdinarySectionMap.Ordinary.frameIso p k n X Y f hp).inv =
    (GlobalDeRham.Comparison.iso p k n X Y f hp).hom := by
  rw [← frameMap_eq, square, targetIso_eq]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryAssemblyCoordinates.Ordinary
