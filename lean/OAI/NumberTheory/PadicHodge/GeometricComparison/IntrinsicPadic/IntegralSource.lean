import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedDeRham
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameSource
import OAI.NumberTheory.PadicHodge.GeometricComparison.MappedSquare

/-! # Integral Source -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralSource.IntrinsicPadicGeometricIntegralSource

noncomputable section

/-! Actual integral quotient and native frame comparisons commute with
geometric pullback after the original crystalline coefficient functor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))} [Smooth X₁.hom] [Smooth X₂.hom]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of (ZMod p)))}
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂)
  (n : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "F" => Functor.mapHomologicalComplex
  (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.coefficients p) (ComplexShape.up ℕ)
local notation "S" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.source (Over.Hom.left u))
local notation "T" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.target (Over.Hom.left u))

def transformation : T ⋙ IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X₂ n ⟶
    S ⋙ IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X₁ n :=
  Functor.whiskerRight (ReducedSource.IntrinsicPadicGeometricReducedSource.transformation p u n) F

def coefficients : ((Affine.MapPairs.AffineMapPairs.Charts u.left)ᵒᵖ ⥤ CochainComplex (ModuleCat (WittVector p (ZMod p))) ℕ) ⥤
    ((Affine.MapPairs.AffineMapPairs.Charts u.left)ᵒᵖ ⥤ CochainComplex (ModuleCat.{2} R) ℕ) :=
  (Functor.whiskeringRight _ _ _).obj F

local notation "G" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralSource.IntrinsicPadicGeometricIntegralSource.coefficients p u

omit [Smooth X₁.hom] in
theorem target_coordinates : (G).map
    (Functor.whiskerLeft T (ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.pdTransformation p X₂ Y₂ f₂ hp₂ n)) =
    Functor.whiskerLeft T (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.transformation p X₂ Y₂ f₂ hp₂ n) := rfl

omit [Smooth X₂.hom] in
theorem source_coordinates : (G).map
    (Functor.whiskerLeft S (ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.pdTransformation p X₁ Y₁ f₁ hp₁ n)) =
    Functor.whiskerLeft S (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.transformation p X₁ Y₁ f₁ hp₁ n) := rfl

theorem frame_coordinates : (G).map
    (Principal.IntrinsicPadicGeometricPrincipalComparison.frameMap p u v f₁ f₂ hp₁ hp₂ hsquare n) =
      FrameSource.IntrinsicPadicGeometricFrameSource.transformation p u v f₁ f₂ hp₁ hp₂ hsquare n := rfl

omit [Smooth X₁.hom] [Smooth X₂.hom] in
theorem map_coordinates : (G).map (ReducedSource.IntrinsicPadicGeometricReducedSource.transformation p u n) =
    transformation p u n := rfl

theorem natural :
    Functor.whiskerLeft T (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.transformation p X₂ Y₂ f₂ hp₂ n) ≫
      FrameSource.IntrinsicPadicGeometricFrameSource.transformation p u v f₁ f₂ hp₁ hp₂ hsquare n =
    transformation p u n ≫
      Functor.whiskerLeft S (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.transformation p X₁ Y₁ f₁ hp₁ n) :=
  MappedSquare.MappedSquareCoordinates.square G
    (Functor.whiskerLeft T (ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.pdTransformation p X₂ Y₂ f₂ hp₂ n))
    (Principal.IntrinsicPadicGeometricPrincipalComparison.frameMap p u v f₁ f₂ hp₁ hp₂ hsquare n)
    (ReducedSource.IntrinsicPadicGeometricReducedSource.transformation p u n)
    (Functor.whiskerLeft S (ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.pdTransformation p X₁ Y₁ f₁ hp₁ n))
    _ _ _ _ (ReducedDeRham.IntrinsicPadicGeometricReducedDeRham.natural p u v f₁ f₂ hp₁ hp₂ hsquare n)
    (target_coordinates p u f₂ hp₂ n) (frame_coordinates p u v f₁ f₂ hp₁ hp₂ hsquare n)
    (map_coordinates p u n) (source_coordinates p u f₁ hp₁ n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralSource.IntrinsicPadicGeometricIntegralSource
