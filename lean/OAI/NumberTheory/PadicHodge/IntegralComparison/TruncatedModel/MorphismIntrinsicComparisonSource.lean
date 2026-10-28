import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameGlobalSourceHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.ExactRefinedGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicSourceHomology

/-! # Morphism Intrinsic Comparison Source -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicComparisonSource.Intrinsic

noncomputable section

section

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
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.DeRham.Comparison.coefficientFunctor p k
local notation "c" => HomologicalComplex.homologyMap
  (MorphismFrameCechHomology.sourceComparison p k n u f₁ hp₁ I₁) i ≫
    Iso.hom (MorphismCommonGlobal.sourceHomologyIso p k n u f₁ I₁ i)
local notation "g" => ModuleCat.ofHom (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallinePullback.pullback v.left
  (MorphismData.Frames.ambient_over p k v) n i)

abbrev sourceFrame :=
  MorphismIntrinsicSourceHomology.IntrinsicStages.sourceCohomology p k n u f₁ hp₁ I₁ i
    (MorphismGlobalTypedHomology.source_new p k n u f₁ I₁ i)
    (MorphismGlobalTypedHomology.source_old p k n f₁ I₁ i)

abbrev sourceCoefficient :=
  sourceFrame p k n u f₁ hp₁ I₁ i (WittVector p k)
    (SmoothWitt.DeRham.Comparison.coefficientFunctor p k)

end

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
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.DeRham.Comparison.coefficientFunctor p k
local notation "c" => HomologicalComplex.homologyMap
  (MorphismFrameCechHomology.sourceComparison p k n u f₁ hp₁ I₁) i ≫
    Iso.hom (MorphismCommonGlobal.sourceHomologyIso p k n u f₁ I₁ i)
local notation "g" => ModuleCat.ofHom (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallinePullback.pullback v.left
  (MorphismData.Frames.ambient_over p k v) n i)

abbrev sourceIsos :=
  sourceCoefficient p k n u f₁ hp₁ I₁ i _ _
    (MorphismIntrinsicCoordinates.Intrinsic.sourceIso p k n f₁ hp₁)
    (MorphismCoefficientCech.ordinarySourceIso p k n u f₁ hp₁)

abbrev sourceMap :=
  sourceIsos p k n u f₁ hp₁ I₁ i
    (MorphismIntrinsicCoordinates.Intrinsic.sourceMap p k n u)

abbrev source :=
  sourceMap p k n u f₁ hp₁ I₁ i
    (MorphismIntrinsicCoordinates.Intrinsic.source p k n u f₁ hp₁).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicComparisonSource.Intrinsic
