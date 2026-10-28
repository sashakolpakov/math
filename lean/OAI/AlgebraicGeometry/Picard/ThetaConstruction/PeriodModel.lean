import OAI.AlgebraicGeometry.Picard.ThetaConstruction.Realization
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport
import OAI.RepresentationTheory.Theta.Geometric.Torus.Derivative
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! # Period Model -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric

noncomputable section

/-! The constructed algebraic model of an ThetaConstruction quotient, together with
actual local holomorphic vector lifts on that model. These lifts are used
to compare algebraic theta transition functions with the original factor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

local instance algebraicPeriodModelIntegral (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left :=
  A.variety.property
local instance algebraicPeriodModelSmooth (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom :=
  A.variety.presentation.smooth

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim}

structure AlgebraicPeriodModel (T : DefinitionsIntegral.MarkedPolarizedTorus dim matrix) where
  abelian : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety
  period : (ProjectivePeriodData.Geometric.projectivePeriodData T).periodTorus ≃ₘ⟮𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData T).space),
    𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel abelian)⟯ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints abelian.toOver
  period_add : ∀ u v, period (u + v) = period u * period v

theorem exists_algebraicPeriodModel (T : DefinitionsIntegral.MarkedPolarizedTorus dim matrix) :
    Nonempty (AlgebraicPeriodModel T) := by
  obtain ⟨A, e, he⟩ :=
    RepresentationTheory.Theta.Geometric.Torus.AbelianModel.CM.Algebraization.AbelianTorusModel.exists_abelian_model_with_group (ProjectivePeriodData.Geometric.projectivePeriodData T)
  exact ⟨⟨A, e, he⟩⟩

namespace AlgebraicPeriodModel
variable {T : DefinitionsIntegral.MarkedPolarizedTorus dim matrix} (M : AlgebraicPeriodModel T)

local instance : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

def periodAddEquiv : (ProjectivePeriodData.Geometric.projectivePeriodData T).periodTorus ≃+
    Additive (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) where
  toFun t := Additive.ofMul (M.period t)
  invFun p := M.period.symm p.toMul
  left_inv := M.period.symm_apply_apply
  right_inv := M.period.apply_symm_apply
  map_add' := M.period_add

def vectorPeriod (v : (ProjectivePeriodData.Geometric.projectivePeriodData T).space) : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver :=
  M.period (QuotientAddGroup.mk v)

theorem vectorPeriod_contMDiff : ContMDiff 𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData T).space)
    𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) ∞ M.vectorPeriod :=
  M.period.contMDiff.comp (ProjectivePeriodData.Geometric.projectivePeriodData T).periodProjection_contMDiff

theorem vectorPeriod_zero : M.vectorPeriod 0 = 1 :=
  congrArg Additive.toMul M.periodAddEquiv.map_zero

theorem vectorPeriod_mfderiv (v : (ProjectivePeriodData.Geometric.projectivePeriodData T).space) :
    mfderiv 𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData T).space) 𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)
      M.vectorPeriod v =
      mfderiv 𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData T).space) 𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)
        M.period (QuotientAddGroup.mk v) := by
  have h := mfderiv_comp v
    (M.period.contMDiff.mdifferentiableAt (x := QuotientAddGroup.mk v) (by simp))
    ((ProjectivePeriodData.Geometric.projectivePeriodData T).periodProjection_contMDiff.mdifferentiableAt (x := v) (by simp))
  rw [(ProjectivePeriodData.Geometric.projectivePeriodData T).periodProjection_mfderiv] at h
  exact h

def periodDifferential : (ProjectivePeriodData.Geometric.projectivePeriodData T).space ≃L[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian :=
  (M.period.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv
    (x := (0 : (ProjectivePeriodData.Geometric.projectivePeriodData T).periodTorus)) (by trivial)

theorem periodDifferential_eq : M.periodDifferential.toContinuousLinearMap =
    mfderiv 𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData T).space) 𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)
      M.vectorPeriod 0 := by
  rw [M.vectorPeriod_mfderiv]
  rfl

def localPeriodDomain (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :=
  ⟨M.period.symm ⁻¹' ((ProjectivePeriodData.Geometric.projectivePeriodData T).periodChart (M.period.symm p)).source,
    ((ProjectivePeriodData.Geometric.projectivePeriodData T).periodChart (M.period.symm p)).open_source.preimage M.period.symm.continuous⟩

def localPeriodLift (p q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) : (ProjectivePeriodData.Geometric.projectivePeriodData T).space :=
  (ProjectivePeriodData.Geometric.projectivePeriodData T).periodChart (M.period.symm p) (M.period.symm q)

theorem mem_localPeriodDomain (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    p ∈ M.localPeriodDomain p := (ProjectivePeriodData.Geometric.projectivePeriodData T).mem_periodChart_source (M.period.symm p)

theorem localPeriodLift_period (p q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (hq : q ∈ M.localPeriodDomain p) : M.vectorPeriod (M.localPeriodLift p q) = q := by
  have h := ((ProjectivePeriodData.Geometric.projectivePeriodData T).periodChart (M.period.symm p)).left_inv hq
  rw [(ProjectivePeriodData.Geometric.projectivePeriodData T).periodChart_symm] at h
  exact (congrArg M.period h).trans (M.period.apply_symm_apply q)

theorem localPeriodLift_contMDiffAt (p q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (hq : q ∈ M.localPeriodDomain p) :
    ContMDiffAt 𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) 𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData T).space) ∞
      (M.localPeriodLift p) q := by
  have hc : ContMDiffAt 𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData T).space) 𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData T).space) ∞
      ((ProjectivePeriodData.Geometric.projectivePeriodData T).periodChart (M.period.symm p)) (M.period.symm q) :=
    (contMDiffOn_chart (I := 𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData T).space))
      (x := M.period.symm p)).contMDiffAt
      (((ProjectivePeriodData.Geometric.projectivePeriodData T).periodChart (M.period.symm p)).open_source.mem_nhds hq)
  exact hc.comp q (M.period.symm.contMDiff q)

end AlgebraicPeriodModel

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric
