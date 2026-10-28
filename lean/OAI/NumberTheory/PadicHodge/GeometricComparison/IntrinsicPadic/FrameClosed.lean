import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage
import OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.WittFrameClosed

/-! # Frame Closed -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameClosed.IntrinsicPadicFrameClosed

noncomputable section

/-! The actual closed map of a native global frame is an open immersion
with image equal to the specified special-fiber affine open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem range_comp_iso {U V Z : Scheme} (a : U ⟶ V) [IsIso a] (b : V ⟶ Z) :
    Set.range (a ≫ b) = Set.range b := by
  change Set.range (b ∘ a) = _
  have hs : Function.Surjective a := a.homeomorph.surjective
  rw [Set.range_comp, Set.range_eq_univ.mpr hs, Set.image_univ]

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ) (U : X.left.Opens) (hU : IsAffineOpen U)

local instance padic : Algebra ℤ_[p] (AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X U
local instance witt : Algebra (WittVector p (ZMod p)) (AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U) :=
  WittAlgebra.PadicWittAlgebra.algebra p (AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U)
local instance special : Algebra (ZMod p) (AffineFrame.IntrinsicPadicAffineFrame.targetRing p X Y f U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (ZMod p) Y (f ⁻¹ᵁ U)

theorem local_isIso : IsIso (AffineFrame.IntrinsicPadicAffineFrame.frame p X Y f hp U hU n).obj.mapToX := by
  let := AffineFrame.IntrinsicPadicAffineFrame.source_flat p X U hU
  exact GeometricComparison.Smooth.WittFrameClosed.SmoothWittFrameClosed.isIso p (ZMod p)
    (AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U) (AffineFrame.IntrinsicPadicAffineFrame.targetRing p X Y f U)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction p X Y f U)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_surjective p X Y f hp U hU)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_kernel p X Y f hp U hU)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_base p X Y f hp U) n

theorem openImmersion : IsOpenImmersion (ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp U hU n).obj.mapToX := by
  let := local_isIso p X Y f hp n U hU
  change IsOpenImmersion ((AffineFrame.IntrinsicPadicAffineFrame.frame p X Y f hp U hU n).obj.mapToX ≫
    ChartImage.IntrinsicPadicOpenFrame.chart p X Y f hp U hU)
  exact IsOpenImmersion.comp _ _

theorem range : Set.range (ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp U hU n).obj.mapToX =
    (f ⁻¹ᵁ U : Set Y.left) := by
  let := local_isIso p X Y f hp n U hU
  exact (range_comp_iso (AffineFrame.IntrinsicPadicAffineFrame.frame p X Y f hp U hU n).obj.mapToX
    (ChartImage.IntrinsicPadicOpenFrame.chart p X Y f hp U hU)).trans
      (ChartImage.IntrinsicPadicOpenFrame.special_affine p X Y f hp U hU).range_fromSpec

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameClosed.IntrinsicPadicFrameClosed
