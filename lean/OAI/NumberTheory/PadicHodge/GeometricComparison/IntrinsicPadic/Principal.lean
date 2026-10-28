import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientRings
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameDiagramPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.PrincipalFrameSquare

/-! # Principal -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Principal.IntrinsicPadicGeometricPrincipalComparison

noncomputable section

/-! The original native principal PD-to-ordinary comparison commutes
with actual geometric pullback on compatible affine pairs. -/

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

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameData.IntrinsicPadicFrameGeometricData
local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁
local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.source (Over.Hom.left u) ⋙ OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor.functor p X₁ Y₁ f₁ hp₁ n
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.target (Over.Hom.left u) ⋙ OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor.functor p X₂ Y₂ f₂ hp₂ n
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagram.IntrinsicPadicFrameGeometricDiagram.transformation p u v f₁ f₂ hp₁ hp₂ hsquare n

local notation "S" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.source (Over.Hom.left u))
local notation "T" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.target (Over.Hom.left u))
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)
local notation "W" => WittVector p (ZMod p)

def frameMap : T ⋙ PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.pdComplexes p X₂ Y₂ f₂ hp₂ n ⟶
    S ⋙ PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.pdComplexes p X₁ Y₁ f₁ hp₁ n :=
  Crystalline.FrameDiagramPullback.CrystallineFrameDiagramPullback.transformation v.left (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n P Q a

theorem natural : frameMap p u v f₁ f₂ hp₁ hp₂ hsquare n ≫
    Functor.whiskerLeft S (PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.iso p X₁ Y₁ f₁ hp₁ n).hom =
      Functor.whiskerLeft T (PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.iso p X₂ Y₂ f₂ hp₂ n).hom ≫
        Functor.whiskerRight (QuotientRings.IntrinsicPadicGeometricQuotientRings.transformation p u v f₁ f₂ hp₁ hp₂ hsquare n)
          (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor W) := by
  apply NatTrans.ext
  funext U
  have h₁ := Crystalline.FrameDiagramPullback.CrystallineFrameDiagramPullback.component v.left (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n P Q a U.unop
  have h₂ := PrincipalFrameSquare.PrincipalGeometricFrameSquare.square (p : W) γ v.left (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n
    ((P).obj U.unop) ((Q).obj U.unop) ((a).app U.unop)
    (PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.ideal_generated p X₁ Y₁ f₁ hp₁ n (Opposite.op U.unop.val.1))
    (PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.ideal_generated p X₂ Y₂ f₂ hp₂ n (Opposite.op U.unop.val.2))
  have h₃ := QuotientRings.IntrinsicPadicGeometricQuotientRings.component p u v f₁ f₂ hp₁ hp₂ hsquare n U.unop
  exact (congrArg (fun m => m ≫ (PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.iso p X₁ Y₁ f₁ hp₁ n).hom.app
    (Opposite.op U.unop.val.1)) h₁).trans
      (h₂.trans (congrArg (fun m => (PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.iso p X₂ Y₂ f₂ hp₂ n).hom.app
        (Opposite.op U.unop.val.2) ≫ (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor W).map m) h₃.symm))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Principal.IntrinsicPadicGeometricPrincipalComparison
