import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicSourceOldCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicSourceIsoCoordinates

/-! # Source Exact Old Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SourceExactOldCoordinates.MorphismIntrinsic

noncomputable section

/-! The original source comparison in the exact frame and global-section
coordinates of the native source pipeline. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  {Y : Over (Spec (CommRingCat.of k))} [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

variable
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

def statement (q : ℕ) : Prop :=
  (MorphismIntrinsicBase.IntrinsicComparison.sourceIso p k n f hp I q).hom =
    Witt.IntrinsicCechComposite.Intrinsic.composite p k (CechSliceResolution.opens p k n X)
      (K := AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ)
        (FrameDiagonalMap.source p k n X Y f hp))
      (L := MorphismGlobalRefinementBase.Maps.sourceSections p k n f I)
      (FrameInjective.Comparison.map p k n X Y f hp I) q
      (T := ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
        (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
          (J := Ideal.span {(p : WittVector p k)})
          (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
          (Witt.Crystalline.wittStructureMap p k Y) n q))
      (Witt.IntrinsicCechCoefficientComposite.Intrinsic.coefficientIso p k
        (CechSliceResolution.opens p k n X)
        (SmoothWitt.DeRham.Comparison.coefficientFunctor p k)
        (((ModuleCat.restrictScalars
          (algebraMap (WittVector p k) (Truncated.Witt.Ring p k n))).mapHomologicalComplex
            (.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total (Truncated.Witt.Ring p k n) X))
        (K := AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ)
          (FrameDiagonalMap.source p k n X Y f hp))
        (MorphismIntrinsicCoordinates.Intrinsic.sourceIso p k n f hp) q).hom
      (MorphismGlobalTypedHomology.sourceOldComparison p k n f I q)

theorem comparison (q : ℕ) : statement p k n f hp I q := by
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SourceExactOldCoordinates.MorphismIntrinsic
