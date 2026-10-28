import OAI.RepresentationTheory.Theta.Geometric.GaugeOpens

/-! # Iso Gauge Holomorphic -/

namespace OAI.RepresentationTheory.Theta.Geometric.IsoGaugeHolomorphic

noncomputable section

/-! Each regular local comparison is holomorphic along the actual period
map, and has the original polarization's translation character. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)
    (fS fT : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (gS gT : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase G.projectiveDimension))
    (e : (AlgebraicQuotient.algebraicThetaQuotient fS.left gS.left).sheaf ≅
      (AlgebraicQuotient.algebraicThetaQuotient fT.left gT.left).sheaf)
    (a : Φ.space) (p : Φ.space → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)

set_option backward.isDefEq.respectTransparency false in
theorem localThetaIsoGauge_differentiableAt [IsIntegral X.left] [Smooth X.hom]
    (i : QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension ×
      QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension) (z : Φ.space)
    (hp : MDifferentiableAt (𝓘(ℂ, Φ.space))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) p z)
    (hmem : (p z).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ IsoFrameUnits.thetaIsoFrameOpen fS.left fT.left gS.left gT.left i)
    (hi : z ∈ GaugeOpens.thetaTranslationGaugeOpen F G a i) :
    DifferentiableAt ℂ (fun w => IsoGaugeCompatibility.localThetaIsoGauge F G fS fT gS gT e i (p w) (w + a) w) z := by
  let U := IsoFrameUnits.thetaIsoFrameOpen fS.left fT.left gS.left gT.left i
  let r : Γ(X.left, U) := IsoFrameUnits.thetaIsoFrameUnitOn fS.left fT.left gS.left gT.left e i U le_rfl
  have hr := OpenRegularFunctionHolomorphic.openRegularFunctionValue_comp_differentiableAt X U r p z hp hmem
  have ht := ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_differentiableAt F G i.2.1 i.2.2 z hi.2.1
  have hs := (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_differentiableAt F G i.1.1 i.1.2 (z + a) hi.1.1).comp z
    (differentiableAt_id.add_const a)
  have H := (hr.fun_mul ht).fun_mul
    (hs.fun_inv (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_ne_zero F G i.1.1 i.1.2 (z + a) hi.1.1 hi.1.2))
  simpa only [IsoGaugeCompatibility.localThetaIsoGauge, div_eq_mul_inv, Function.comp_def, id_eq, U, r] using H

theorem localThetaIsoGauge_translates (hdeg : G.degree = F.degree + 1)
    (hp : ∀ l : Φ.periodIntegerLattice, ∀ z, p (z + l.val) = p z)
    (i : QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension ×
      QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension)
    (l : Φ.periodIntegerLattice) (z : Φ.space)
    (hi : z ∈ GaugeOpens.thetaTranslationGaugeOpen F G a i) :
    IsoGaugeCompatibility.localThetaIsoGauge F G fS fT gS gT e i (p (z + l.val)) (z + l.val + a) (z + l.val) *
        J.value l (z + a) =
      J.value l z * IsoGaugeCompatibility.localThetaIsoGauge F G fS fT gS gT e i (p z) (z + a) z := by
  have hza : z + l.val + a = (z + a) + l.val := by abel
  simp only [IsoGaugeCompatibility.localThetaIsoGauge, hp l z, hza, ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_translates F G hdeg]
  field_simp [J.value_ne_zero l (z + a),
    ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_ne_zero F G i.1.1 i.1.2 (z + a) hi.1.1 hi.1.2]

end

end OAI.RepresentationTheory.Theta.Geometric.IsoGaugeHolomorphic
