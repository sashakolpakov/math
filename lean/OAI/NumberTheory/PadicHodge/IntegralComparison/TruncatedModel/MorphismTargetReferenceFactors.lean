import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetOldCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TargetCommonReferenceCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetReferenceData

/-! # Morphism Target Reference Factors -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetReferenceFactors.ReferenceCoordinates

noncomputable section

/-! The two complete coordinate factors of the native target comparison,
checked independently of the naturality proof. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (sq : f₁ ≫ u.left = v.left ≫ f₂)
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))
  (I₂ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₂) n))

attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

def leftStatement (i : ℕ) : Prop :=
  (MorphismIntrinsicBase.IntrinsicComparison.targetIso p k n f₂ hp₂ I₂ i).hom ≫
      ModuleCat.ofHom (BoundedCrystalline.CrystallinePullback.pullback v.left
        (MorphismData.Frames.ambient_over p k v) n i) =
    (Witt.ReferenceCechComposite.Reference.composite.{1,2}
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
      (CechSliceResolution.opens p k n X₂)
      (MorphismRawEq.OldFrameCoordinates.coefficientMap p k n f₂ hp₂ I₂) i
      (MorphismTargetIsoCoordinates.homologyIso p k n f₂ hp₂ i).hom
      (GlobalEdge.InjectiveCech.homologyIso p k n X₂ Y₂ f₂ I₂ i).hom) ≫
      ModuleCat.ofHom (BoundedCrystalline.CrystallinePullback.pullback v.left
        (MorphismData.Frames.ambient_over p k v) n i)

omit [IsSeparated Y₁.hom] in
theorem left_coordinates (i : ℕ) : leftStatement p k n v f₂ hp₂ I₂ i := by
  unfold leftStatement
  dsimp only [MorphismIntrinsicBase.IntrinsicComparison.targetIso, Iso.trans_hom]
  exact congrArg
    (fun c => c ≫ ModuleCat.ofHom (BoundedCrystalline.CrystallinePullback.pullback v.left
      (MorphismData.Frames.ambient_over p k v) n i))
    (MorphismTargetOldCoordinates.comparison p k n f₂ hp₂ I₂ i)

def rightStatement (i : ℕ) : Prop :=
  (SmoothWitt.DeRham.Comparison.coefficientFunctor p k).map
      (homologyMap (MorphismIntrinsicCoordinates.Intrinsic.targetMap p k n u) i) ≫
    (SmoothWitt.DeRham.Comparison.coefficientFunctor p k).map
      (homologyMap (MorphismOrdinaryCech.Ordinary.ordinaryMap p k n u) i) ≫
    MorphismIntrinsicBase.IntrinsicComparison.commonComparison p k n u f₁ hp₁ I₁ i =
    (SmoothWitt.DeRham.Comparison.coefficientFunctor p k).map
      (homologyMap (MorphismIntrinsicCoordinates.Intrinsic.targetMap p k n u) i) ≫
    (SmoothWitt.DeRham.Comparison.coefficientFunctor p k).map
      (homologyMap (MorphismOrdinaryCech.Ordinary.ordinaryMap p k n u) i) ≫
    ModuleCech.CoefficientComposite.composite
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) (WittVector p k)
      (MorphismCover.pairs p k n u)
      (SmoothWitt.DeRham.Comparison.coefficientFunctor p k)
      (MorphismCommonIsoCoordinates.source p k n u)
      (K := AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ)
        ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left).op ⋙
          FrameDiagonalMap.source p k n X₁ Y₁ f₁ hp₁))
      (L := MorphismCommonGlobal.sourceSections p k n u f₁ I₁)
      (TargetCommonIsoCoordinates.Morphism.iso p k n u f₁ hp₁)
      (MorphismFrameInjectiveHomotopy.sourceComparison p k n u f₁ hp₁ I₁)
      i (MorphismGlobalTypedHomology.sourceNewComparison p k n u f₁ I₁ i)

theorem right_coordinates (i : ℕ) : rightStatement p k n u f₁ hp₁ I₁ i := by
  unfold rightStatement
  have h := TargetCommonReferenceCoordinates.MorphismReference.comparison
    p k n u f₁ hp₁ I₁ i
  change _ at h
  delta TargetCommonReferenceCoordinates.MorphismReference.statement at h
  exact congrArg
    (fun c =>
      (SmoothWitt.DeRham.Comparison.coefficientFunctor p k).map
        (homologyMap (MorphismIntrinsicCoordinates.Intrinsic.targetMap p k n u) i) ≫
      (SmoothWitt.DeRham.Comparison.coefficientFunctor p k).map
        (homologyMap (MorphismOrdinaryCech.Ordinary.ordinaryMap p k n u) i) ≫ c)
    h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetReferenceFactors.ReferenceCoordinates
