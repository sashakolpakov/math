import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicPresheafSourceEndpoints
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalSourceCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalTypedHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicCoordinates

/-! # Intrinsic Source Endpoints Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicSourceEndpointsCoordinates

noncomputable section

/-! The original source frame and global cone maps with the native coefficient
category fixed before the injective resolution is chosen. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
namespace MorphismIntrinsic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂)
  {Y₁ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom]
  (f₁ : Y₁.left ⟶ X₁.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))

attribute [local instance] MorphismGlobalSourceCohomology.sourceTypedEdgeEpi

abbrev core :=
  IntrinsicPresheafSourceEndpoints.MorphismIntrinsic.source p k n u _
    (MorphismGlobalRefinementBase.Maps.sourceSections p k n f₁ I₁)
    (FrameInjective.Comparison.map p k n X₁ Y₁ f₁ hp₁ I₁)
    (MorphismFrameInjectiveHomotopy.sourceComparison p k n u f₁ hp₁ I₁)
    (MorphismFrameRefinementCoordinates.Comparison.source_coordinates p k n u f₁ hp₁ I₁)

abbrev data :=
  core p k n u f₁ hp₁ I₁
    (MorphismGlobalCone.sourceGlobal p k n I₁)
    (MorphismGlobalTypedEdges.sourceCone p k n f₁ I₁)
    (MorphismGlobalTypedEdges.sourceOld p k n f₁ I₁)
    (MorphismGlobalTypedEdges.sourceNew p k n u f₁ I₁)
    (MorphismGlobalTypedEdges.source_old p k n f₁ I₁)
    (MorphismGlobalTypedEdges.source_new p k n u f₁ I₁)

end MorphismIntrinsic

/-! The native source comparison with its original three global homology maps
and its bounded crystalline output fixed explicitly. -/
namespace MorphismIntrinsic
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂)
  {Y₁ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom]
  (f₁ : Y₁.left ⟶ X₁.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))

attribute [local instance] MorphismGlobalSourceCohomology.sourceTypedEdgeEpi

abbrev homology (q : ℕ) :=
  data p k n u f₁ hp₁ I₁ q
    _
    (MorphismGlobalTypedHomology.sourceOldComparison p k n f₁ I₁ q)
    (MorphismGlobalTypedHomology.sourceNewComparison p k n u f₁ I₁ q)
    (MorphismGlobalTypedHomology.sourceGlobalComparison p k n I₁ q)
    (MorphismGlobalTypedHomology.source_new p k n u f₁ I₁ q)
    (MorphismGlobalTypedHomology.source_old p k n f₁ I₁ q)

end

/-! The original source coefficient isomorphisms and refinement map in the
native module category. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂)
  {Y₁ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom]
  (f₁ : Y₁.left ⟶ X₁.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))

abbrev isos (q : ℕ) :=
  homology p k n u f₁ hp₁ I₁ q _ _
    (MorphismIntrinsicCoordinates.Intrinsic.sourceIso p k n f₁ hp₁)
    (MorphismCoefficientCech.ordinarySourceIso p k n u f₁ hp₁)

abbrev map (q : ℕ) :=
  isos p k n u f₁ hp₁ I₁ q
    (MorphismIntrinsicCoordinates.Intrinsic.sourceMap p k n u)

abbrev comparison (q : ℕ) :=
  MorphismIntrinsic.map p k n u f₁ hp₁ I₁ q
    (MorphismIntrinsicCoordinates.Intrinsic.source p k n u f₁ hp₁).symm

end MorphismIntrinsic

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicSourceEndpointsCoordinates
