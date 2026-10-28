import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.OpenPairs
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ResolutionDiagram
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LargeOpenMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.ComplexBifunctorChange

/-! # Section Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionMap.IntrinsicPadicGeometricSectionMap

noncomputable section

/-! Geometric pullback of the original native section bifunctors
over compatible pairs of integral affine opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))} [Smooth X₁.hom] [Smooth X₂.hom]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of (ZMod p)))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂) (n : ℕ)

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameData.IntrinsicPadicFrameGeometricData
local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁
local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) (Over.Hom.left v) (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n
local notation "SX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.functor (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w₁ n
local notation "SY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.functor (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w₂ n

def sourceSections := SX ⋙
  (Functor.whiskeringLeft _ _ (ModuleCat.{2} Rcoeff)).obj (OpenPairs.IntrinsicPadicGeometricOpenPairs.source p u f₁).op

def targetSections := SY ⋙
  (Functor.whiskeringLeft _ _ (ModuleCat.{2} Rcoeff)).obj (OpenPairs.IntrinsicPadicGeometricOpenPairs.target p u f₂).op

instance sourceSections_additive : (sourceSections p u f₁ n).Additive := by
  dsimp only [sourceSections]
  infer_instance

instance targetSections_additive : (targetSections p u f₂ n).Additive := by
  dsimp only [targetSections]
  infer_instance

def transformation : targetSections p u f₂ n ⟶ T ⋙ sourceSections p u f₁ n :=
  Functor.whiskerRight (Bounded.LargeOpenMap.BoundedGeometricLargeOpenMap.functorMap v.left (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n)
    ((Functor.whiskeringLeft _ _ (ModuleCat.{2} Rcoeff)).obj (OpenPairs.IntrinsicPadicGeometricOpenPairs.target p u f₂).op) ≫
      Functor.whiskerLeft (T ⋙ SX)
        ((Functor.whiskeringLeft _ _ (ModuleCat.{2} Rcoeff)).map
          (OpenPairs.IntrinsicPadicGeometricOpenPairs.restriction p u v f₁ f₂ hsquare))

variable
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))

local instance sourceSeparated : IsSeparated w₁ := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance
local instance targetSeparated : IsSeparated w₂ := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

local notation "P" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.target (Over.Hom.left u) ⋙ OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor.functor p X₂ Y₂ f₂ hp₂ n) ⋙
  BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor w₂ n
local notation "Q" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.source (Over.Hom.left u) ⋙ OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor.functor p X₁ Y₁ f₁ hp₁ n) ⋙
  BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor w₁ n

def complexes : P ⋙ (targetSections p u f₂ n).mapHomologicalComplex (.up ℕ) ⟶
    Q ⋙ (sourceSections p u f₁ n).mapHomologicalComplex (.up ℕ) :=
  Section.ComplexBifunctorChange.SectionComplexBifunctorChange.complexes T (targetSections p u f₂ n) (sourceSections p u f₁ n) P Q
    (ResolutionDiagram.IntrinsicPadicGeometricResolutionDiagram.transformation p u v f₁ f₂ hp₁ hp₂ hsquare n)
    (transformation p u v f₁ f₂ hsquare n)

def rows : Section.ComplexBifunctor.SectionComplexBifunctor.functor (targetSections p u f₂ n) P ⟶
    Section.ComplexBifunctor.SectionComplexBifunctor.functor (sourceSections p u f₁ n) Q :=
  Section.ComplexBifunctorChange.SectionComplexBifunctorChange.rows T (targetSections p u f₂ n) (sourceSections p u f₁ n) P Q
    (ResolutionDiagram.IntrinsicPadicGeometricResolutionDiagram.transformation p u v f₁ f₂ hp₁ hp₂ hsquare n)
    (transformation p u v f₁ f₂ hsquare n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionMap.IntrinsicPadicGeometricSectionMap
