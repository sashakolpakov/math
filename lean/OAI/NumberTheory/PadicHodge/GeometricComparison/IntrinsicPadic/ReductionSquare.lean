import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientRings
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralAlgebra
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientReductionCoordinates

/-! # Reduction Square -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReductionSquare.IntrinsicPadicGeometricReductionSquare

noncomputable section

/-! The actual integral pullback and actual frame pullback commute with
original coefficient reduction on every compatible affine pair. -/

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

theorem natural :
    Functor.whiskerLeft (Affine.MapPairs.AffineMapPairs.target u.left).op
      (QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap.transformation p X₂ Y₂ f₂ hp₂ n) ≫
      QuotientRings.IntrinsicPadicGeometricQuotientRings.transformation p u v f₁ f₂ hp₁ hp₂ hsquare n =
    IntegralAlgebra.IntrinsicPadicGeometricIntegralAlgebra.transformation p u ≫
      Functor.whiskerLeft (Affine.MapPairs.AffineMapPairs.source u.left).op
        (QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap.transformation p X₁ Y₁ f₁ hp₁ n) := by
  apply NatTrans.ext
  funext U
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  change (QuotientRings.IntrinsicPadicGeometricQuotientRings.transformation p u v f₁ f₂ hp₁ hp₂ hsquare n).app U
      ((QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap.transformation p X₂ Y₂ f₂ hp₂ n).app (Opposite.op U.unop.val.2) x) =
    (QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap.transformation p X₁ Y₁ f₁ hp₁ n).app (Opposite.op U.unop.val.1)
      ((IntegralAlgebra.IntrinsicPadicGeometricIntegralAlgebra.transformation p u).app U x)
  have h₁ := QuotientReductionCoordinates.IntrinsicPadicQuotientReductionCoordinates.component p X₂ Y₂ f₂ hp₂ n U.unop.val.2 x
  have h₂ := ConcreteCategory.congr_hom
    (QuotientRings.IntrinsicPadicGeometricQuotientRings.component p u v f₁ f₂ hp₁ hp₂ hsquare n U.unop)
    (FrameGenerators.IntrinsicPadicFrameGenerators.generators p X₂ Y₂ f₂ hp₂ n U.unop.val.2.val U.unop.val.2.property x)
  have h₃ := FrameMap.IntrinsicPadicFrameGeometricMap.map_mk p u v f₁ f₂ hp₁ hp₂ hsquare
    U.unop.val.2.val U.unop.val.1.val U.unop.val.2.property U.unop.val.1.property U.unop.property n x
  have h₄ := QuotientReductionCoordinates.IntrinsicPadicQuotientReductionCoordinates.component p X₁ Y₁ f₁ hp₁ n U.unop.val.1
    ((IntegralAlgebra.IntrinsicPadicGeometricIntegralAlgebra.transformation p u).app U x)
  exact (congrArg ((QuotientRings.IntrinsicPadicGeometricQuotientRings.transformation p u v f₁ f₂ hp₁ hp₂ hsquare n).app U) h₁).trans
    (h₂.trans (h₃.trans h₄.symm))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReductionSquare.IntrinsicPadicGeometricReductionSquare
