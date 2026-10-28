import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismData
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.FrameSquare

/-! # Morphism Diagram -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismDiagram

noncomputable section

/-! Actual finite-level model maps commute with affine restriction and
give natural transformations on compatible pairs of charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [Smooth X₁.hom] [Smooth X₂.hom]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))}
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (sq : f₁ ≫ u.left = v.left ≫ f₂)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose v.left
  (MorphismData.Frames.ambient_over p k v) n
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor.functor p k n X₁ Y₁ f₁ hp₁
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor.functor p k n X₂ Y₂ f₂ hp₂

section Restriction

variable (U U' : X₂.left.affineOpens) (V V' : X₁.left.affineOpens)
  (hU : U ⟶ U') (hV : V ⟶ V')
  (hu : V.val ≤ u.left ⁻¹ᵁ U.val) (hu' : V'.val ≤ u.left ⁻¹ᵁ U'.val)

local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismData.Frames.map p k n u v f₁ f₂ hp₁ hp₂ sq
  U.val V.val U.property V.property hu
local notation "a'" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismData.Frames.map p k n u v f₁ f₂ hp₁ hp₂ sq
  U'.val V'.val U'.property V'.property hu'

theorem ring_square : ((P).map hV).hom.ringMap.toRingHom.comp (a').hom.ringMap.toRingHom =
    (a).hom.ringMap.toRingHom.comp ((Q).map hU).hom.ringMap.toRingHom := by
  ext x
  change FrameFunctor.integralMap p k n X₁ V.val V'.val (leOfHom hV)
    (MorphismData.integralMap p k n u U'.val V'.val hu' x) =
      MorphismData.integralMap p k n u U.val V.val hu
        (FrameFunctor.integralMap p k n X₂ U.val U'.val (leOfHom hU) x)
  have hs := u.left.appLE_map hu' (homOfLE (leOfHom hV)).op
  have ht := u.left.map_appLE hu (homOfLE (leOfHom hU)).op
  exact ConcreteCategory.congr_hom (hs.trans ht.symm) x

theorem natural : (G).map ((P).map hV) ≫ a' = a ≫ (Q).map hU :=
  GeometricComparison.Bounded.FrameSquare.BoundedGeometricFrameSquare.square v.left (MorphismData.Frames.ambient_over p k v) n
    ((P).map hV) ((Q).map hU) a a'
    (ring_square p k n u v f₁ f₂ hp₁ hp₂ sq U U' V V' hU hV hu hu')

end Restriction

def transformation : AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left ⋙ P ⋙ G ⟶
    AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left ⋙ Q where
  app A := MorphismData.Frames.map p k n u v f₁ f₂ hp₁ hp₂ sq
    A.val.2.val A.val.1.val A.val.2.property A.val.1.property A.property
  naturality A D h := natural p k n u v f₁ f₂ hp₁ hp₂ sq
    A.val.2 D.val.2 A.val.1 D.val.1
    ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left).map h) ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left).map h)
    A.property D.property

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismDiagram
