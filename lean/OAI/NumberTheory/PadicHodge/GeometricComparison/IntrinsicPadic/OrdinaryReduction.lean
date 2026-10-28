import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedSource
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReductionSquare
import OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinaryReduction

/-! # Ordinary Reduction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.OrdinaryReduction.IntrinsicPadicGeometricOrdinaryReduction

noncomputable section

/-! Original ordinary de Rham coefficient reduction commutes with
actual geometric pullback on compatible native affine pairs. -/

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

local notation "W" => WittVector p (ZMod p)
local notation "Ip" => (Ideal.span {(p : WittVector p (ZMod p))}) ^ (n + 1)
local notation "S" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.source (Over.Hom.left u))
local notation "T" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.target (Over.Hom.left u))
local notation "A₁" => S ⋙ OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X₁
local notation "A₂" => T ⋙ OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X₂
local notation "B₁" => S ⋙ OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.rings p X₁ Y₁ f₁ hp₁ n
local notation "B₂" => T ⋙ OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.rings p X₂ Y₂ f₂ hp₂ n
local notation "q₁" => Functor.whiskerLeft S (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap.transformation p X₁ Y₁ f₁ hp₁ n)
local notation "q₂" => Functor.whiskerLeft T (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap.transformation p X₂ Y₂ f₂ hp₂ n)

theorem natural :
    Functor.whiskerLeft T (ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.ordinaryTransformation p X₂ Y₂ f₂ hp₂ n) ≫
      Functor.whiskerRight (QuotientRings.IntrinsicPadicGeometricQuotientRings.transformation p u v f₁ f₂ hp₁ hp₂ hsquare n)
        (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor W) =
    ReducedSource.IntrinsicPadicGeometricReducedSource.transformation p u n ≫
      Functor.whiskerLeft S (ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.ordinaryTransformation p X₁ Y₁ f₁ hp₁ n) :=
  OrdinaryReduction.OrdinaryReductionDiagramSquare.natural W Ip A₂ B₂ A₁ B₁ q₂ q₁
    (fun U => QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap.annihilation p X₂ Y₂ f₂ hp₂ n ((T).obj U))
    (fun U => QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap.annihilation p X₁ Y₁ f₁ hp₁ n ((S).obj U))
    (IntegralAlgebra.IntrinsicPadicGeometricIntegralAlgebra.transformation p u)
    (QuotientRings.IntrinsicPadicGeometricQuotientRings.transformation p u v f₁ f₂ hp₁ hp₂ hsquare n)
    (ReductionSquare.IntrinsicPadicGeometricReductionSquare.natural p u v f₁ f₂ hp₁ hp₂ hsquare n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.OrdinaryReduction.IntrinsicPadicGeometricOrdinaryReduction
