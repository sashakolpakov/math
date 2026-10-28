import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.OrdinaryReduction
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Principal
import OAI.NumberTheory.PadicHodge.IntegralComparison.InverseCoordinateHomology

/-! # Reduced De Rham -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedDeRham.IntrinsicPadicGeometricReducedDeRham

noncomputable section

/-! The original integral coefficient quotient-to-PD-frame comparison
commutes with every actual compatible geometric map of native affine pairs. -/

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
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Principal.IntrinsicPadicGeometricPrincipalComparison.frameMap p u v f₁ f₂ hp₁ hp₂ hsquare n
local notation "b" => Functor.whiskerRight
  (QuotientRings.IntrinsicPadicGeometricQuotientRings.transformation p u v f₁ f₂ hp₁ hp₂ hsquare n)
  (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor W)
local notation "c₂" => Functor.whiskerLeft T (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.ordinaryTransformation p X₂ Y₂ f₂ hp₂ n)
local notation "c₁" => Functor.whiskerLeft S (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.ordinaryTransformation p X₁ Y₁ f₁ hp₁ n)
local notation "e₂" => Functor.isoWhiskerLeft T (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.iso p X₂ Y₂ f₂ hp₂ n)
local notation "e₁" => Functor.isoWhiskerLeft S (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.iso p X₁ Y₁ f₁ hp₁ n)
local notation "d" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedSource.IntrinsicPadicGeometricReducedSource.transformation p u n

theorem inverse_comparison : b ≫ (e₁).inv = (e₂).inv ≫ a :=
  IntegralComparison.InverseCoordinateHomology.inverse e₂ e₁ a b
    (Principal.IntrinsicPadicGeometricPrincipalComparison.natural p u v f₁ f₂ hp₁ hp₂ hsquare n)

theorem natural :
    Functor.whiskerLeft T (ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.pdTransformation p X₂ Y₂ f₂ hp₂ n) ≫ a =
      d ≫ Functor.whiskerLeft S (ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.pdTransformation p X₁ Y₁ f₁ hp₁ n) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun m => c₂ ≫ m) (inverse_comparison p u v f₁ f₂ hp₁ hp₂ hsquare n).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun m => m ≫ (e₁).inv)
          (OrdinaryReduction.IntrinsicPadicGeometricOrdinaryReduction.natural p u v f₁ f₂ hp₁ hp₂ hsquare n)).trans
          (Category.assoc _ _ _))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedDeRham.IntrinsicPadicGeometricReducedDeRham
