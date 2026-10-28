import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicHomology
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined

/-! # Morphism Target Iso Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetIsoCoordinates

noncomputable section

/-! The native small-cover coefficient isomorphism, with its original
presheaf-total target fixed before applying homology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  {Y : Over (Spec (CommRingCat.of k))} [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

def source : CochainComplex (ModuleCat (WittVector p k)) ℕ :=
  ((ModuleCat.restrictScalars
      (algebraMap (WittVector p k) (Truncated.Witt.Ring p k n))).mapHomologicalComplex
        (.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.total (Truncated.Witt.Ring p k n) X)

def target : CochainComplex
    (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ :=
  AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.total.{1,2}
    (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
    (CechSliceResolution.opens p k n X)
    (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ)
      (FrameDiagonalMap.source p k n X Y f hp))

def iso :
    ((SmoothWitt.DeRham.Comparison.coefficientFunctor p k).mapHomologicalComplex (.up ℕ)).obj
      (source p k n (X := X)) ≅ target p k n f hp :=
  MorphismIntrinsicCoordinates.Intrinsic.targetIso p k n f hp

attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

def homologyIso (q : ℕ) := GeometricComparison.ExactHomology.ExactHomologyComparison.iso
  (SmoothWitt.DeRham.Comparison.coefficientFunctor p k) (.up ℕ)
  (source p k n (X := X)) (target p k n f hp) (iso p k n f hp) q

omit [IsSeparated Y.hom] in
theorem comparison (q : ℕ) :
    (MorphismIntrinsicHomology.Intrinsic.targetIso p k n f hp q).hom =
      (homologyIso p k n f hp q).hom := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetIsoCoordinates
