import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ParameterRestriction

/-! # Parameter Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ParameterRefinement.Chart

noncomputable section

/-! A specified point parameter chart is refined by its actual
Jacobian determinant. Its equations and parameters remain literal
restrictions, and an existing second frame restricts to the same open. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

private theorem frame_reindex {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {r n : ℕ} (b : Module.Basis (Fin r) A M) (h : r=n) (i : Fin r) :
    (b.reindex (finCongr h)) (Fin.cast h i) = b i := by
  subst n
  simp

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {N : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra PointParameterData.Chart.ambientAlgebra
variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R N)
  [IsClosedImmersion f.left] (z : Spec (CommRingCat.of R) ⟶ X.left)
  (g : ℕ) (U : (Projective.IntrinsicOverlap.Intrinsic.space R N).Opens) (hU : IsAffineOpen U)

abbrev _root_.OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PointParameterData.Chart.ParameterData.frameFunction (D : PointParameterData.Chart.ParameterData X f z g U hU) : Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,U) :=
  Affine.ParameterFrameNeighborhood.determinant R X (Projective.IntrinsicOverlap.Intrinsic.model R N) f U hU
    (ConormalKoszulPurity.conormalVectors Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,U)
      (Projective.LocalAdjunction.ideal X f U hU) D.equations D.generates) D.parameters
    ((Projective.AmbientAdjunction.differentialBasis D.coordinate U hU D.below_coordinate).reindex
      (finCongr D.dimension.symm))

variable [Smooth X.hom]

omit [IsNoetherianRing R] in
theorem _root_.OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PointParameterData.Chart.ParameterData.frame_preimage (D : PointParameterData.Chart.ParameterData X f z g U hU) :
    f.left ⁻¹ᵁ (Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen (D.frameFunction X f z g U hU) = f.left ⁻¹ᵁ U := by
  let : Smooth (Projective.IntrinsicOverlap.Intrinsic.model R N).hom := Projective.SpaceSmooth.smooth
  exact Affine.ParameterFrameNeighborhood.preimage R X (Projective.IntrinsicOverlap.Intrinsic.model R N) f U hU
    (ConormalKoszulPurity.conormalVectors Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,U)
      (Projective.LocalAdjunction.ideal X f U hU) D.equations D.generates) D.parameters
    ((Projective.AmbientAdjunction.differentialBasis D.coordinate U hU D.below_coordinate).reindex
      (finCongr D.dimension.symm))
    D.conormalBasis D.conormalBasis_apply D.quotientBasis D.quotientBasis_apply

omit [IsNoetherianRing R] in
theorem _root_.OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PointParameterData.Chart.ParameterData.frame_contains (D : PointParameterData.Chart.ParameterData X f z g U hU) :
    ⊤ ≤ z ⁻¹ᵁ (f.left ⁻¹ᵁ (Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen (D.frameFunction X f z g U hU)) := by
  rw [D.frame_preimage X f z g U hU]
  exact D.contains

def _root_.OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PointParameterData.Chart.ParameterData.framed (D : PointParameterData.Chart.ParameterData X f z g U hU) :
    PointParameterData.Chart.Data X f z g ((Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen (D.frameFunction X f z g U hU))
      (hU.basicOpen (D.frameFunction X f z g U hU)) := by
  let sI := ConormalKoszulPurity.conormalVectors Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,U)
    (Projective.LocalAdjunction.ideal X f U hU) D.equations D.generates
  let b0 := (Projective.AmbientAdjunction.differentialBasis D.coordinate U hU D.below_coordinate).reindex
    (finCongr D.dimension.symm)
  let bV := Affine.ParameterFrameNeighborhood.basis R X (Projective.IntrinsicOverlap.Intrinsic.model R N) f U hU sI D.parameters b0
  have hbV := Affine.ParameterFrameNeighborhood.basis_eq R X (Projective.IntrinsicOverlap.Intrinsic.model R N) f U hU sI D.parameters b0
  refine {
    toParameterData := D.principal X f z g U hU (D.frameFunction X f z g U hU)
      (D.frame_contains X f z g U hU)
    ambientBasis := bV.reindex (finCongr D.dimension)
    ambientBasis_apply := ?_ }
  funext i
  exact (frame_reindex bV D.dimension i).trans (congrFun hbV i)

omit [IsNoetherianRing R] in
theorem _root_.OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PointParameterData.Chart.ParameterData.framed_parameters (D : PointParameterData.Chart.ParameterData X f z g U hU) :
    (D.framed X f z g U hU).parameters =
      IdealSheafPrincipalEquations.sequence U (D.frameFunction X f z g U hU) D.parameters := rfl

def _root_.OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PointParameterData.Chart.Data.restrictFor (D : PointParameterData.Chart.Data X f z g U hU) (P : PointParameterData.Chart.ParameterData X f z g U hU) :
    PointParameterData.Chart.Data X f z g ((Projective.IntrinsicOverlap.Intrinsic.space R N).basicOpen (P.frameFunction X f z g U hU))
      (hU.basicOpen (P.frameFunction X f z g U hU)) :=
  D.principal X f z g U hU (P.frameFunction X f z g U hU) (P.frame_contains X f z g U hU)

omit [IsNoetherianRing R] in
theorem _root_.OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PointParameterData.Chart.Data.restrictFor_parameters (D : PointParameterData.Chart.Data X f z g U hU) (P : PointParameterData.Chart.ParameterData X f z g U hU) :
    (D.restrictFor X f z g U hU P).parameters =
      IdealSheafPrincipalEquations.sequence U (P.frameFunction X f z g U hU) D.parameters := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ParameterRefinement.Chart
