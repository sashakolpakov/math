import OAI.RepresentationTheory.Theta.Geometric.DolbeaultBoundary
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Dolbeault Quotient -/

namespace OAI.RepresentationTheory.Theta.Geometric.DolbeaultQuotient

noncomputable section

/-! The concrete complex vector-space quotient of closed global
Dolbeault one-forms by scalar derivatives gives the actual holomorphic H1 group. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] (M : Type) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℂ, E) ∞ M]

def globalDbarLinear : AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E (⊤ : Opens M) 0 →ₗ[ℂ] DolbeaultBoundary.ClosedDbarOneForm E M :=
  (AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD (⊤ : Opens M) 0).codRestrict (DolbeaultBoundary.ClosedDbarOneForm E M)
    (fun s => AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD_squared ⊤ 0 s)

theorem globalDbarLinear_toAddMonoidHom :
    (globalDbarLinear E M).toAddMonoidHom = DolbeaultBoundary.globalDbarDerivative E M := rfl

abbrev DolbeaultOneSpace := DolbeaultBoundary.ClosedDbarOneForm E M ⧸ LinearMap.range (globalDbarLinear E M)

variable [FiniteDimensional ℂ E]

instance globalDbarDerivative_range_normal : (DolbeaultBoundary.globalDbarDerivative E M).range.Normal := by
  rw [DolbeaultBoundary.globalDbarDerivative_range]
  exact AddMonoidHom.normal_ker (DolbeaultBoundary.holomorphicDbarClass E M)

def dolbeaultOneClassEquiv [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M] :
    DolbeaultOneSpace E M ≃+ CategoryTheory.Sheaf.H (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) 1 :=
  (QuotientAddGroup.quotientAddEquivOfEq (DolbeaultBoundary.globalDbarDerivative_range E M)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (DolbeaultBoundary.holomorphicDbarClass E M)
      (DolbeaultBoundary.holomorphicDbarClass_surjective E M))

theorem dolbeaultOneClassEquiv_mk [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M]
    (a : DolbeaultBoundary.ClosedDbarOneForm E M) :
    dolbeaultOneClassEquiv E M (Submodule.Quotient.mk a) = DolbeaultBoundary.holomorphicDbarClass E M a := rfl

end

end OAI.RepresentationTheory.Theta.Geometric.DolbeaultQuotient
