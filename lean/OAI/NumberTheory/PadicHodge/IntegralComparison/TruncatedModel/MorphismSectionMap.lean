import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismOpenPairs
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismResolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LargeOpenMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.ComplexBifunctorChange

/-! # Morphism Section Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSectionMap

noncomputable section

/-! Geometric pullback of the original native section bifunctors
over compatible pairs of integral affine opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))} [Smooth X₁.hom] [Smooth X₂.hom]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (sq : f₁ ≫ u.left = v.left ≫ f₂)

open OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismData.Frames
local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

local instance coefficientRing : Ring Rcoeff := (inferInstance : CommRing Rcoeff).toRing

local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₁
local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₂
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Over.Hom.left v) (MorphismData.Frames.ambient_over p k v) n
local notation "SX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.functor (p := p)
  (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) w₁ n
local notation "SY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.functor (p := p)
  (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) w₂ n

def sourceSections := SX ⋙
  (Functor.whiskeringLeft _ _ (ModuleCat.{2} Rcoeff)).obj (MorphismOpenPairs.source p k n u f₁).op

def targetSections := SY ⋙
  (Functor.whiskeringLeft _ _ (ModuleCat.{2} Rcoeff)).obj (MorphismOpenPairs.target p k n u f₂).op

instance sourceSections_additive : (sourceSections p k n u f₁).Additive := by
  dsimp only [sourceSections]
  infer_instance

instance targetSections_additive : (targetSections p k n u f₂).Additive := by
  dsimp only [targetSections]
  infer_instance

def transformation : targetSections p k n u f₂ ⟶ T ⋙ sourceSections p k n u f₁ :=
  Functor.whiskerRight (GeometricComparison.Bounded.LargeOpenMap.BoundedGeometricLargeOpenMap.functorMap v.left (MorphismData.Frames.ambient_over p k v) n)
    ((Functor.whiskeringLeft _ _ (ModuleCat.{2} Rcoeff)).obj (MorphismOpenPairs.target p k n u f₂).op) ≫
      Functor.whiskerLeft (T ⋙ SX)
        ((Functor.whiskeringLeft _ _ (ModuleCat.{2} Rcoeff)).map
          (MorphismOpenPairs.restriction p k n u v f₁ f₂ sq))

variable
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

local instance sourceSeparated : IsSeparated w₁ := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance
local instance targetSeparated : IsSeparated w₂ := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local notation "P" => Functor.op (OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target (Over.Hom.left u) ⋙ OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor.functor p k n X₂ Y₂ f₂ hp₂) ⋙
  GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor w₂ n
local notation "Q" => Functor.op (OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source (Over.Hom.left u) ⋙ OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor.functor p k n X₁ Y₁ f₁ hp₁) ⋙
  GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor w₁ n

def complexes : P ⋙ (targetSections p k n u f₂).mapHomologicalComplex (.up ℕ) ⟶
    Q ⋙ (sourceSections p k n u f₁).mapHomologicalComplex (.up ℕ) :=
  GeometricComparison.Section.ComplexBifunctorChange.SectionComplexBifunctorChange.complexes T (targetSections p k n u f₂) (sourceSections p k n u f₁) P Q
    (MorphismResolution.transformation p k n u v f₁ f₂ hp₁ hp₂ sq)
    (transformation p k n u v f₁ f₂ sq)

def rows : GeometricComparison.Section.ComplexBifunctor.SectionComplexBifunctor.functor (targetSections p k n u f₂) P ⟶
    GeometricComparison.Section.ComplexBifunctor.SectionComplexBifunctor.functor (sourceSections p k n u f₁) Q :=
  GeometricComparison.Section.ComplexBifunctorChange.SectionComplexBifunctorChange.rows T (targetSections p k n u f₂) (sourceSections p k n u f₁) P Q
    (MorphismResolution.transformation p k n u v f₁ f₂ hp₁ hp₂ sq)
    (transformation p k n u v f₁ f₂ sq)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSectionMap
