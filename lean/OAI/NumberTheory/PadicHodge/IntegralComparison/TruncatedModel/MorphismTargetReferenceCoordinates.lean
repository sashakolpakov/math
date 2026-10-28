import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicTargetEndpointCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicTargetLeftCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicTargetRightCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetReferenceData

/-! # Morphism Target Reference Coordinates -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetReferenceCoordinates.ReferenceEquality

/-! Discharge the two native target endpoint equalities using the original
comparison maps and their checked coordinate identities. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (sq : f₁ ≫ u.left = v.left ≫ f₂)
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))
  (I₂ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₂) n))

variable (i : ℕ)

attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

abbrev endpoints :=
  IntrinsicTargetEndpointCoordinates.MorphismIntrinsic.target p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ i
    ((MorphismIntrinsicBase.IntrinsicComparison.targetIso p k n f₂ hp₂ I₂ i).hom ≫
      ModuleCat.ofHom (BoundedCrystalline.CrystallinePullback.pullback v.left
        (MorphismData.Frames.ambient_over p k v) n i))
    ((SmoothWitt.DeRham.Comparison.coefficientFunctor p k).map
        (HomologicalComplex.homologyMap
          (MorphismIntrinsicCoordinates.Intrinsic.targetMap p k n u) i) ≫
      (SmoothWitt.DeRham.Comparison.coefficientFunctor p k).map
        (HomologicalComplex.homologyMap
          (MorphismOrdinaryCech.Ordinary.ordinaryMap p k n u) i) ≫
      MorphismIntrinsicBase.IntrinsicComparison.commonComparison p k n u f₁ hp₁ I₁ i)

abbrev withLeft :=
  endpoints p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ i
    (IntrinsicTargetLeftCoordinates.MorphismIntrinsic.comparison
      p k n v f₂ hp₂ I₂ i)

abbrev closed :=
  withLeft p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ i
    (IntrinsicTargetRightCoordinates.MorphismIntrinsic.comparison
      p k n u f₁ hp₁ I₁ i)

include sq in
theorem comparison :
    MorphismTargetReferenceData.ReferenceCoordinates.statement
      p k n u v f₁ f₂ hp₁ hp₂ I₁ I₂ i := by
  unfold MorphismTargetReferenceData.ReferenceCoordinates.statement
  exact closed p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ i

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetReferenceCoordinates.ReferenceEquality

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetReferenceCoordinates.Reference

/-! The checked raw target square expressed through the original
native frame comparison isomorphisms. -/
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

include sq in
theorem target (i : ℕ) : MorphismTargetReferenceData.ReferenceCoordinates.statement p k n u v f₁ f₂ hp₁ hp₂ I₁ I₂ i :=
  ReferenceEquality.comparison
    p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ i

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetReferenceCoordinates.Reference

end

end OAI
