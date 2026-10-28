import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ParameterRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ParameterReplacement

/-! # Parameter Lift Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint

noncomputable section

/-! The prescribed source parameters remain the literal pullbacks
of the framed ambient lifts after principal refinement. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {N : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra PointParameterData.Chart.ambientAlgebra
variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R N)
  [IsClosedImmersion f.left] (z : Spec (CommRingCat.of R) ⟶ X.left)
  (g : ℕ) (U : (Projective.IntrinsicOverlap.Intrinsic.space R N).Opens) (hU : IsAffineOpen U)

omit [IsNoetherianRing R] in
theorem PointParameterData.Chart.ParameterData.principal_lift (D : PointParameterData.Chart.ParameterData X f z g U hU)
    (r : Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,U)) (hc : ⊤ ≤ z ⁻¹ᵁ (f.left ⁻¹ᵁ (Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen r)) (i : Fin g) :
    f.left.app ((Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen r)
      ((D.principal X f z g U hU r hc).parameters i) =
    X.left.presheaf.map (homOfLE (f.left.preimage_mono ((Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen_le r))).op
      (f.left.app U (D.parameters i)) :=
  ConcreteCategory.congr_hom (f.left.naturality (homOfLE ((Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen_le r)).op)
    (D.parameters i)

variable [Smooth X.hom]

omit [IsNoetherianRing R] in
theorem PointParameterData.Chart.ParameterData.framed_lift (D : PointParameterData.Chart.ParameterData X f z g U hU) (i : Fin g) :
    f.left.app ((Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen (D.frameFunction X f z g U hU))
      ((D.framed X f z g U hU).parameters i) =
    X.left.presheaf.map
      (homOfLE (f.left.preimage_mono ((Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen_le (D.frameFunction X f z g U hU)))).op
      (f.left.app U (D.parameters i)) :=
  D.principal_lift X f z g U hU (D.frameFunction X f z g U hU) (D.frame_contains X f z g U hU) i

variable [IsClosedImmersion z] (hz : z ≫ X.hom = 𝟙 _)
  (D : PointParameterData.Chart.ParameterData X f z g U hU)
  (t : Fin g → Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))
  (ht : Ideal.span (Set.range t) = z.ker.ideal ⟨f.left ⁻¹ᵁ U,hU.preimage f.left⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular
    (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U)) (List.ofFn t))
  (b : Module.Basis (Fin g) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))
    Ω[Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U)⁄R])
  (hb : ∀ i, b i = KaehlerDifferential.D R _ (t i))

omit [IsNoetherianRing R] in
theorem PointParameterData.Chart.ParameterData.replaced_framed_lift (i : Fin g) :
    let P := D.replace X f z hz g U hU t ht hreg b hb
    f.left.app ((Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen (P.frameFunction X f z g U hU))
      ((P.framed X f z g U hU).parameters i) =
    X.left.presheaf.map
      (homOfLE (f.left.preimage_mono ((Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen_le (P.frameFunction X f z g U hU)))).op
      (t i) := by
  dsimp only
  rw [PointParameterData.Chart.ParameterData.framed_lift, PointParameterData.Chart.ParameterData.replace_lift]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint
