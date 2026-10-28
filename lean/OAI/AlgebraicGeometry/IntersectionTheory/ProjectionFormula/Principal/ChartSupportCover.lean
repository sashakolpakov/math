import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartEquations
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ModuleSupportCover
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalCodimension

/-! # Chart Support Cover -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartSupportCover

noncomputable section

/-! Fixed finite ambient support covers control the full zero loci
of every chosen numerator and denominator on the finite affine charts. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ChartGerm.FiniteSupportCharts OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartEquations

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ)
  [SmoothOfRelativeDimension m X.structureMap] (W : X.DimensionCycleSupport k)
  (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField) (hg : g ≠ 0)

def module (i : Affine.ChartGerm.FiniteSupportCharts.Index X W.val × Bool) : ModuleCat (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1) :=
  .of _ (QuotSMulTop (ChartEquations.equation X W.val g hg i) ((Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1) ⧸ (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i.1).asIdeal))

instance (i : Affine.ChartGerm.FiniteSupportCharts.Index X W.val × Bool) : Module.Finite (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1) (module X k W g hg i) := by
  unfold module
  infer_instance

include m

theorem exists_data (i : Affine.ChartGerm.FiniteSupportCharts.Index X W.val × Bool) :
    ∃ S : Finset (IrreducibleCloseds X.carrier),
      (∀ B ∈ S, k + 1 ≤ X.supportCodimension B) ∧
      ∀ z ∈ Module.support (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1) (module X k W g hg i),
        ∃ B ∈ S, Affine.ChartGerm.FiniteSupportCharts.chart X W.val i.1 z ∈ (B : Set X.carrier) := by
  apply Affine.ModuleSupportCover.exists_data (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1) X (k + 1)
    (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i.1) (module X k W g hg i)
  apply Affine.PrincipalCodimension.bound X m k (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i.1) (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i.1)
  · exact (congrArg X.supportCodimension (Affine.ChartGerm.FiniteSupportCharts.prime_support X W.val i.1)).trans W.property
  · exact ChartEquations.equation_avoid X W.val g hg i

def supports (i : Affine.ChartGerm.FiniteSupportCharts.Index X W.val × Bool) : Finset (IrreducibleCloseds X.carrier) :=
  (exists_data X m k W g hg i).choose

theorem codimension (i : Affine.ChartGerm.FiniteSupportCharts.Index X W.val × Bool) (B : IrreducibleCloseds X.carrier)
    (hB : B ∈ supports X m k W g hg i) : k + 1 ≤ X.supportCodimension B :=
  (exists_data X m k W g hg i).choose_spec.1 B hB

theorem covers (i : Affine.ChartGerm.FiniteSupportCharts.Index X W.val × Bool) (z : PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1))
    (hz : z ∈ Module.support (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1) (module X k W g hg i)) :
    ∃ B ∈ supports X m k W g hg i, Affine.ChartGerm.FiniteSupportCharts.chart X W.val i.1 z ∈ (B : Set X.carrier) :=
  (exists_data X m k W g hg i).choose_spec.2 z hz

def Index : Type := Σ i : Affine.ChartGerm.FiniteSupportCharts.Index X W.val × Bool, supports X m k W g hg i

instance : Finite (Index X m k W g hg) := by unfold Index; infer_instance

def family (i : Index X m k W g hg) : IrreducibleCloseds X.carrier := i.2.val

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartSupportCover
