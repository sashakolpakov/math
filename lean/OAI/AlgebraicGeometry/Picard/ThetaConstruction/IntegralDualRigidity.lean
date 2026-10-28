import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualTranslation
import OAI.RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.IsoGauge

/-! # Integral Dual Rigidity -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! An actual algebraic translation preserving the primitive ThetaConstruction theta
bundle belongs to the constructed integral dual lattice. The proof uses
the actual holomorphic gauge extracted from its sheaf isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} (T : DefinitionsIntegral.MarkedPolarizedTorus g E) (hE : E.transpose = -E)

theorem IntegralDualRigidity.Geometric.translationGauge_mem_integralDual (a : DefinitionsIntegral.Tangent g) (c : DefinitionsIntegral.Tangent g → ℂ)
    (hc : Differentiable ℂ c) (hc0 : c 0 ≠ 0)
    (htrans : ∀ (l : (ProjectivePeriodData.Geometric.projectivePeriodData T).periodIntegerLattice) w,
      c (w + (show DefinitionsIntegral.Tangent g from l.val)) * (PolarizationFactor.Geometric.polarizationFactor T hE).value l (w + a) =
        (PolarizationFactor.Geometric.polarizationFactor T hE).value l w * c w) : a ∈ T.integralDualLattice := by
  let : CompactSpace ((DefinitionsIntegral.Tangent g) ⧸ T.lattice) := T.compact
  let : DiscreteTopology T.lattice := T.discrete
  have hshift : ∀ (l : T.lattice) w,
      RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.adjustedTranslationGauge T.riemannForm a c (w + (show DefinitionsIntegral.Tangent g from l.val)) =
        RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.hermitianTranslationCharacter T.riemannForm a l.val * RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.adjustedTranslationGauge T.riemannForm a c w :=
    RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.adjustedTranslationGauge_translates (DefinitionsIntegral.Geometric.integralLatticeBasis T) (DefinitionsIntegral.Geometric.integralLatticeForm T)
      T.lattice.subtype T.riemannForm a c htrans
  intro v hv
  have hχ := RepresentationTheory.Theta.Geometric.UnitaryAutomorphyRigidity.unitaryAutomorphy_trivial T.lattice (RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.adjustedTranslationGauge T.riemannForm a c)
    (fun m => RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.hermitianTranslationCharacter T.riemannForm a m.val)
    (fun m => RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.hermitianTranslationCharacter_unitary _ T.hermitian a m.val)
    (RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.adjustedTranslationGauge_differentiable _ a c hc) hshift
    (by simpa [RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.adjustedTranslationGauge] using hc0) ⟨v, hv⟩
  obtain ⟨m, hm⟩ := (RepresentationTheory.Theta.Geometric.HermitianTranslationCharacter.hermitianTranslationCharacter_eq_one_iff _ T.hermitian a v).mp hχ
  exact Submodule.mem_one.mpr ⟨m, hm.symm⟩

variable {T} (M : PeriodModel.Geometric.AlgebraicPeriodModel T)

include hE in
theorem PeriodModel.Geometric.AlgebraicPeriodModel.nativeTranslation_mem_integralDual (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (PolarizationFactor.Geometric.polarizationFactor T hE))
    (hdeg : V.degree = U.degree + 1)
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (jV : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map jV (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))
    (a : DefinitionsIntegral.Tangent g)
    (u : ((RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left jV.left).pullback
      (RepresentationTheory.Theta.Geometric.AlgebraicTranslation.abelianTranslation M.abelian (M.period (QuotientAddGroup.mk a))).left).sheaf ≅
        (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left jV.left).sheaf) : a ∈ T.integralDualLattice := by
  obtain ⟨c, hc, hcn, htrans⟩ := RepresentationTheory.Theta.Geometric.Intrinsic.IsoGauge.exists_holomorphic_translationGauge_of_native_iso U V hdeg
    M.abelian M.period M.period_add f jV hf hg a u
  exact IntegralDualRigidity.Geometric.translationGauge_mem_integralDual T hE a c hc (hcn 0) htrans

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
