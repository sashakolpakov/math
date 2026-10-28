import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel
import OAI.RepresentationTheory.Theta.Geometric.ChosenTorusRingAction

/-! # Dual Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualAction

noncomputable section

/-! The integral CM action preserves the dual lattice and algebraizes
on its actual abelian model. The reference lattice isogeny intertwines
the two constructed integral scheme actions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}

namespace ReferenceAnalyticFiber

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber.action_preserves_dual (F : Fiber.ReferenceAnalyticFiber P z) (hP : P.IsAdmissible)
    (a : NumberField.RingOfIntegers E) (u : Fiber.ReferenceTangent s) (hu : u ∈ F.dualLattice) :
    F.action a u ∈ F.dualLattice := by
  intro v hv
  have hv' := F.action_preserves_lattice hP
    (NumberField.IsCMField.ringOfIntegersComplexConj E a) v hv
  have h := hu (F.action (NumberField.IsCMField.ringOfIntegersComplexConj E a) v) hv'
  change (F.form (F.action a u) v).im ∈ (1 : Submodule ℤ ℝ)
  exact (congrArg Complex.im (F.form_rosati a u v)).symm ▸ h

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber.dualQuotientAction (F : Fiber.ReferenceAnalyticFiber P z) (hP : P.IsAdmissible) :
    NumberField.RingOfIntegers E →+* AddMonoid.End (F.dualPeriodData hP).periodTorus :=
  (F.dualPeriodData hP).quotientRingAction F.action (F.action_preserves_dual hP)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber.latticeTorusMap_action (F : Fiber.ReferenceAnalyticFiber P z) (hP : P.IsAdmissible)
    (a : NumberField.RingOfIntegers E) (t : F.periodData.periodTorus) :
    F.latticeTorusMap hP (F.quotientAction hP a t) =
      F.dualQuotientAction hP a (F.latticeTorusMap hP t) := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective t
  rfl

end ReferenceAnalyticFiber

namespace ReferenceDualModel

variable (D : DualModel.ReferenceDualModel F hP)

local instance : IsIntegral D.abelian.toOver.left := D.abelian.variety.property
local instance : Smooth D.abelian.toOver.hom := D.abelian.variety.presentation.smooth

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel.exists_algebraic_action :
    ∃ r : NumberField.RingOfIntegers E →+* AbelianScheme.TateComparison.End.IntegralEnd D.abelian.toOver,
      ∀ a t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianScheme.TateComparison.End.endSchemeMap D.abelian.toOver (r a)) (D.period t) =
        D.period (F.dualQuotientAction hP a t) :=
  RepresentationTheory.Theta.Geometric.ChosenTorusRingAction.exists_ring_action_on_period_model (F.dualPeriodData hP) F.action
    (F.action_preserves_dual hP) D.abelian D.period D.period_add

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel.functorAction : NumberField.RingOfIntegers E →+* AbelianScheme.TateComparison.End.IntegralEnd D.abelian.toOver :=
  D.exists_algebraic_action.choose

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel.integralAction : ActionData.IntegralAction (NumberField.RingOfIntegers E) D.abelianScheme :=
  Integral.FunctorAction.integralActionOfFunctorAction D.abelianScheme D.functorAction

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel.period_action (a : NumberField.RingOfIntegers E) (t : (F.dualPeriodData hP).periodTorus) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianScheme.TateComparison.End.endSchemeMap D.abelian.toOver (D.functorAction a)) (D.period t) =
      D.period (F.dualQuotientAction hP a t) := D.exists_algebraic_action.choose_spec a t

end ReferenceDualModel

namespace ReferenceLatticeIsogeny

variable {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {D : DualModel.ReferenceDualModel F hP}
    (p : IsogenyKernel.ReferenceLatticeIsogeny M D)

local instance _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny.source_integral : IsIntegral M.abelianScheme.scheme.left := M.abelian.variety.property
local instance _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny.target_proper : IsProper D.abelianScheme.scheme.hom := D.abelian.variety.presentation.projective.isProper

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny.integralAction_intertwining (a : NumberField.RingOfIntegers E) :
    M.integralAction.map a ≫ p.isogeny.hom = p.isogeny.hom ≫ D.integralAction.map a := by
  apply Albanese.Construction.ClosedPoints.hom_ext_of_points
  intro x
  obtain ⟨t, rfl⟩ := M.period.surjective x
  let f : M.abelian.toOver ⟶ D.abelian.toOver := p.isogeny.hom
  exact (congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) (M.period_action a t)).trans
    ((p.period_eq (F.quotientAction hP a t)).trans
      ((congrArg D.period (F.latticeTorusMap_action hP a t)).trans
        ((D.period_action a (F.latticeTorusMap hP t)).symm.trans
          (congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
            (AbelianScheme.TateComparison.End.endSchemeMap D.abelian.toOver (D.functorAction a))) (p.period_eq t).symm))))

end ReferenceLatticeIsogeny

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualAction
