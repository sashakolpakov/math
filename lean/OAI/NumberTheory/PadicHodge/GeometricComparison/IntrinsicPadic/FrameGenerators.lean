import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicFrameRestriction
import OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.WittFrameGenerators
import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.PostcompositionGenerators

/-! # Frame Generators -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameGenerators.IntrinsicPadicFrameGenerators

noncomputable section

/-! A surjective generating family stated directly in the native global frame
ring, keeping quotient identifications out of subsequent categorical laws. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local instance padic (U : X.left.Opens) : Algebra ℤ_[p] (AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X U
local instance witt (U : X.left.Opens) : Algebra (WittVector p (ZMod p)) (AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U) :=
  WittAlgebra.PadicWittAlgebra.algebra p (AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U)
local instance special (U : X.left.Opens) : Algebra (ZMod p) (AffineFrame.IntrinsicPadicAffineFrame.targetRing p X Y f U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (ZMod p) Y (f ⁻¹ᵁ U)

def localGenerators (U : X.left.Opens) (hU : IsAffineOpen U) :
    AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U → (AffineFrame.IntrinsicPadicAffineFrame.frame p X Y f hp U hU n).obj.ring := by
  letI := AffineFrame.IntrinsicPadicAffineFrame.source_flat p X U hU
  exact GeometricComparison.Smooth.WittFrameGenerators.SmoothWittFrameGenerators.generators p (ZMod p)
    (AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U) (AffineFrame.IntrinsicPadicAffineFrame.targetRing p X Y f U)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction p X Y f U)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_surjective p X Y f hp U hU)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_kernel p X Y f hp U hU)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_base p X Y f hp U) n

theorem local_surjective (U : X.left.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (localGenerators p X Y f hp n U hU) := by
  let := AffineFrame.IntrinsicPadicAffineFrame.source_flat p X U hU
  exact GeometricComparison.Smooth.WittFrameGenerators.SmoothWittFrameGenerators.surjective p (ZMod p)
    (AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U) (AffineFrame.IntrinsicPadicAffineFrame.targetRing p X Y f U)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction p X Y f U)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_surjective p X Y f hp U hU)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_kernel p X Y f hp U hU)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_base p X Y f hp U) n

def postGenerators (U : X.left.Opens) (hU : IsAffineOpen U) :
    AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U →
      (ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp U hU n).obj.ring :=
  GeometricComparison.Smooth.WittFrameGenerators.SmoothWittFrameGenerators.postcompose (ChartImage.IntrinsicPadicOpenFrame.chart p X Y f hp U hU)
    (ChartImage.IntrinsicPadicOpenFrame.chart_over_witt p X Y f hp U hU) n
    (AffineFrame.IntrinsicPadicAffineFrame.frame p X Y f hp U hU n) (localGenerators p X Y f hp n U hU)

theorem post_surjective (U : X.left.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (postGenerators p X Y f hp n U hU) :=
  GeometricComparison.Smooth.WittFrameGenerators.SmoothWittFrameGenerators.postcompose_surjective (ChartImage.IntrinsicPadicOpenFrame.chart p X Y f hp U hU)
    (ChartImage.IntrinsicPadicOpenFrame.chart_over_witt p X Y f hp U hU) n
    (AffineFrame.IntrinsicPadicAffineFrame.frame p X Y f hp U hU n) (localGenerators p X Y f hp n U hU)
    (local_surjective p X Y f hp n U hU)

def generators (U : X.left.Opens) (hU : IsAffineOpen U) :
    AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U →
      (ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp U hU n).obj.ring :=
  Ideal.Quotient.mk ((Ideal.span {(p : AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U)}) ^ (n + 1))

theorem generators_eq_post (U : X.left.Opens) (hU : IsAffineOpen U) :
    generators p X Y f hp n U hU = postGenerators p X Y f hp n U hU := rfl

theorem surjective (U : X.left.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (generators p X Y f hp n U hU) :=
  (generators_eq_post p X Y f hp n U hU).symm ▸ post_surjective p X Y f hp n U hU

theorem local_map (U V : X.left.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ≤ V) (a : AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X V) :
    (PadicFrameRestriction.IntrinsicPadicFrameRestriction.localMap p X Y f hp U V hU hV hUV n).hom.ringMap
      (localGenerators p X Y f hp n V hV a) =
    localGenerators p X Y f hp n U hU (FrameRestrictionData.IntrinsicPadicFrameRestrictionData.integralMap p X U V hUV a) := rfl

theorem map (U V : X.left.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ≤ V) (a : AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X V) :
    (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp U V hU hV hUV n).hom.ringMap
      (generators p X Y f hp n V hV a) =
    generators p X Y f hp n U hU (FrameRestrictionData.IntrinsicPadicFrameRestrictionData.integralMap p X U V hUV a) := by
  rw [PadicFrameRestriction.IntrinsicPadicFrameRestriction.map_ringMap]
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameGenerators.IntrinsicPadicFrameGenerators
