import OAI.RepresentationTheory.Theta.Geometric.Period.Algebraization
import OAI.RepresentationTheory.Theta.Geometric.AbelianScheme
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.ComplexLevel

/-! # Models -/

namespace OAI.RepresentationTheory.Theta.Geometric.Period.Models.ActiveHeckeThetaData

noncomputable section

/-! Chosen algebraic models for the already constructed explicit period
tori. These are outputs of the proved algebraization theorem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

structure _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.PeriodModel (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) where
  abelian : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety
  period : (D.canonicalPeriodData hg x).periodTorus ≃ₘ⟮
    𝓘(ℂ, (D.canonicalPeriodData hg x).space), 𝓘(ℂ, AlgebraicAction.AbelianModel abelian)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints abelian.toOver
  action : NumberField.RingOfIntegers E →+* AlgebraicGeometry.AbelianScheme.TateComparison.End.IntegralEnd abelian.toOver
  period_add : ∀ u v, period (u + v) = period u * period v
  period_action : ∀ a t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap abelian.toOver (action a)) (period t) =
    period (D.canonicalQuotientAction hg x a t)

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.periodModel_nonempty (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) : Nonempty (D.PeriodModel hg x) := by
  obtain ⟨A, e, r, he, hr⟩ := D.exists_canonical_abelian_model_with_action hg x
  exact ⟨⟨A, e, r, he, hr⟩⟩

def _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.periodModel (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) : D.PeriodModel hg x :=
  Classical.choice (D.periodModel_nonempty hg x)

namespace PeriodModel

variable {D} {hg : D.pel.HasIntegralModelGeometry} {x : D.domain} (M : D.PeriodModel hg x)

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.PeriodModel.dimension : AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension M.abelian.toOver.hom = 3 * s := by
  have h := AbelianScheme.abelian_model_dimension (D.canonicalPeriodData hg x) M.abelian M.period
  change AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension M.abelian.toOver.hom =
    Module.finrank ℂ (Fin s → Fin 3 → ℂ) at h
  rw [Module.finrank_pi_fintype] at h
  simpa only [Module.finrank_fin_fun, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, Nat.mul_comm] using h

def _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.PeriodModel.abelianScheme : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase where
  scheme := M.abelian.toOver
  group := M.abelian.group
  commutative := M.abelian.commutative
  proper := M.abelian.variety.presentation.projective.isProper
  smoothDimension := by
    rw [← M.dimension]
    exact AlgebraicGeometry.Betti.SmoothDimension.Realization.smoothOfFunctionFieldDimension M.abelian.toOver.hom
  connected := (AbelianScheme.abelianSchemeOfVariety M.abelian).connected

def _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.PeriodModel.fullLevel : M.abelianScheme.FullLevel D.pel.level := by
  have h := hg.fullLevel
  let : NeZero D.pel.level := ⟨by omega⟩
  exact AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.ComplexLevel.fullLevel M.abelianScheme M.abelian.variety.presentation.projective D.pel.level

end PeriodModel

end

end OAI.RepresentationTheory.Theta.Geometric.Period.Models.ActiveHeckeThetaData
