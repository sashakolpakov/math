import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SourceExactIsoCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.IntrinsicCechCoefficientComposite

/-! # Intrinsic Source Iso Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicSourceIsoCoordinates.MorphismIntrinsic

noncomputable section

/-! The native source coefficient isomorphism in the exact refined-total
coordinates, before choosing an injective resolution. -/
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

def iso (q : ℕ) :=
  Witt.IntrinsicCechCoefficientComposite.Intrinsic.coefficientIso p k
    (CechSliceResolution.opens p k n X)
    (SmoothWitt.DeRham.Comparison.coefficientFunctor p k)
    (((ModuleCat.restrictScalars
      (algebraMap (WittVector p k) (Truncated.Witt.Ring p k n))).mapHomologicalComplex
        (.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total (Truncated.Witt.Ring p k n) X))
    (K := AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ)
      (FrameDiagonalMap.source p k n X Y f hp))
    (MorphismIntrinsicCoordinates.Intrinsic.sourceIso p k n f hp) q

omit [IsSeparated Y.hom] in
theorem comparison (q : ℕ) :
    (MorphismIntrinsicHomology.Intrinsic.sourceIso p k n f hp q).hom =
      (iso p k n f hp q).hom := by
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicSourceIsoCoordinates.MorphismIntrinsic
