import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameLocalSquare

/-! # Frame Ring Square -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameRingSquare.IntrinsicPadicFrameGeometricRingSquare

noncomputable section

/-! The original global native frame square follows from the checked
local quotient-ring square and its unchanged postcomposition coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))} [Smooth X₁.hom] [Smooth X₂.hom]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of (ZMod p)))}
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂)
  (U U' : X₂.left.affineOpens) (V V' : X₁.left.affineOpens)
  (hU : U ⟶ U') (hV : V ⟶ V')
  (hu : V.val ≤ u.left ⁻¹ᵁ U.val) (hu' : V'.val ≤ u.left ⁻¹ᵁ U'.val) (n : ℕ)

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameData.IntrinsicPadicFrameGeometricData
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose v.left (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor.functor p X₁ Y₁ f₁ hp₁ n
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor.functor p X₂ Y₂ f₂ hp₂ n
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameMap.IntrinsicPadicFrameGeometricMap.map p u v f₁ f₂ hp₁ hp₂ hsquare
  U.val V.val U.property V.property hu n
local notation "a'" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameMap.IntrinsicPadicFrameGeometricMap.map p u v f₁ f₂ hp₁ hp₂ hsquare
  U'.val V'.val U'.property V'.property hu' n

local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X₁ V.val
local notation "B" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X₁ V'.val
local notation "C" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X₂ U.val
local notation "D" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X₂ U'.val
local notation "QA" => A ⧸ (Ideal.span {(p : A)}) ^ (n + 1)
local notation "QB" => B ⧸ (Ideal.span {(p : B)}) ^ (n + 1)
local notation "QC" => C ⧸ (Ideal.span {(p : C)}) ^ (n + 1)
local notation "QD" => D ⧸ (Ideal.span {(p : D)}) ^ (n + 1)
local notation "r₁" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicFrameRestriction.IntrinsicPadicFrameRestriction.localMap p X₁ Y₁ f₁ hp₁
  V.val V'.val V.property V'.property (leOfHom hV) n
local notation "r₂" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicFrameRestriction.IntrinsicPadicFrameRestriction.localMap p X₂ Y₂ f₂ hp₂
  U.val U'.val U.property U'.property (leOfHom hU) n
local notation "b" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameMap.IntrinsicPadicFrameGeometricMap.localMap p u v f₁ f₂ hp₁ hp₂ hsquare
  U.val V.val U.property V.property hu n
local notation "b'" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameMap.IntrinsicPadicFrameGeometricMap.localMap p u v f₁ f₂ hp₁ hp₂ hsquare
  U'.val V'.val U'.property V'.property hu' n

theorem left_coordinates : ((P).map hV).hom.ringMap.toRingHom.comp (a').hom.ringMap.toRingHom =
    (r₁).hom.ringMap.toRingHom.comp (b').hom.ringMap.toRingHom :=
  congrArg₂ (fun (r : QB →+* QA) (s : QD →+* QB) => r.comp s)
    (congrArg DividedPowers.DPMorphism.toRingHom
      (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map_ringMap p X₁ Y₁ f₁ hp₁
        V.val V'.val V.property V'.property (leOfHom hV) n))
    (FrameMap.IntrinsicPadicFrameGeometricRingCoordinates.ringHom p u v f₁ f₂ hp₁ hp₂ hsquare
      U'.val V'.val U'.property V'.property hu' n)

theorem right_coordinates : (a).hom.ringMap.toRingHom.comp ((Q).map hU).hom.ringMap.toRingHom =
    (b).hom.ringMap.toRingHom.comp (r₂).hom.ringMap.toRingHom :=
  congrArg₂ (fun (r : QC →+* QA) (s : QD →+* QC) => r.comp s)
    (FrameMap.IntrinsicPadicFrameGeometricRingCoordinates.ringHom p u v f₁ f₂ hp₁ hp₂ hsquare
      U.val V.val U.property V.property hu n)
    (congrArg DividedPowers.DPMorphism.toRingHom
      (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map_ringMap p X₂ Y₂ f₂ hp₂
        U.val U'.val U.property U'.property (leOfHom hU) n))

theorem ringHom : ((P).map hV).hom.ringMap.toRingHom.comp (a').hom.ringMap.toRingHom =
    (a).hom.ringMap.toRingHom.comp ((Q).map hU).hom.ringMap.toRingHom :=
  (left_coordinates p u v f₁ f₂ hp₁ hp₂ hsquare U' V V' hV hu' n).trans
    ((FrameLocalSquare.IntrinsicPadicFrameGeometricLocalSquare.square p u v f₁ f₂ hp₁ hp₂ hsquare U U' V V' hU hV hu hu' n).trans
      (right_coordinates p u v f₁ f₂ hp₁ hp₂ hsquare U U' V hU hu n).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameRingSquare.IntrinsicPadicFrameGeometricRingSquare
