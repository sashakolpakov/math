import OAI.RepresentationTheory.Theta.Geometric.GlobalDolbeaultForms
import OAI.RepresentationTheory.Theta.Geometric.DolbeaultQuotient

/-! # Closed Pure Dolbeault Map -/

namespace OAI.RepresentationTheory.Theta.Geometric.ClosedPureDolbeaultMap

noncomputable section

section

/-! The canonical complex-linear map from actual closed global
antiholomorphic one-forms to the concrete Dolbeault quotient. -/

set_option backward.isDefEq.respectTransparency false
open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] (M : Type) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℂ, E) ∞ M]

def globalPureOneOnTop (a : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M 0 1) : AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E (⊤ : Opens M) 1 :=
  ⟨Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ a.val, AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldBidegree.openManifoldHasBidegree_onOpen a.property ⊤⟩

theorem globalPureOneOnTop_dbar (a : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M 0 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime a = 0) :
    AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD ⊤ 1 (globalPureOneOnTop E M a) = 0 := by
  apply Subtype.ext
  change AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD 0 1 1 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ a.val) = 0
  have h := congrArg Subtype.val ha
  rw [Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime_coe, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_self] at h
  exact (AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD_onOpen (⊤ : Opens M) a).trans
    ((congrArg (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤) h).trans (map_zero _))

def globalDbarClosedForm (a : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M 0 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime a = 0) : DolbeaultBoundary.ClosedDbarOneForm E M :=
  ⟨globalPureOneOnTop E M a, globalPureOneOnTop_dbar E M a ha⟩

theorem globalDbarClosedForm_of_global (a : DolbeaultBoundary.ClosedDbarOneForm E M) :
    globalDbarClosedForm E M (GlobalDolbeaultForms.closedDbarOneGlobal a) (GlobalDolbeaultForms.closedDbarOneGlobal_dbar a) = a := by
  apply Subtype.ext
  apply Subtype.ext
  exact GlobalDolbeaultForms.closedDbarOneGlobal_onTop a

theorem pureOne_dbar_zero_of_d_zero (a : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M 0 1)
    (ha : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a.val = 0) : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime a = 0 := by
  apply Subtype.ext
  rw [Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime_coe, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_self,
    AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.manifoldDolbeaultDoublePrimeForm_apply, ha, map_zero, smul_zero, sub_zero, smul_zero]
  rfl

abbrev ClosedType01Forms :=
  LinearMap.ker ((Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (E := E) (M := M) (n := 1)).comp
    (Analysis.DifferentialForms.Manifold.ManifoldBidegree.pureManifoldFormSubmodule E M 0 1).subtype)

def closedType01ToDbarForm : ClosedType01Forms E M →ₗ[ℂ] DolbeaultBoundary.ClosedDbarOneForm E M where
  toFun a := globalDbarClosedForm E M a.val (pureOne_dbar_zero_of_d_zero E M a.val a.property)
  map_add' a b := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤).map_add a.val.val b.val.val
  map_smul' c a := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤).map_smul c a.val.val

def closedType01ToDolbeault : ClosedType01Forms E M →ₗ[ℂ] DolbeaultQuotient.DolbeaultOneSpace E M :=
  (LinearMap.range (DolbeaultQuotient.globalDbarLinear E M)).mkQ.comp (closedType01ToDbarForm E M)

end

/-! The actual global/open-top identifications preserve scalar derivatives
and detect equality of the original global forms. -/

set_option backward.isDefEq.respectTransparency false
open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] (M : Type) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℂ, E) ∞ M]

theorem closedDbarOneGlobal_global (a : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M 0 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime a = 0) :
    GlobalDolbeaultForms.closedDbarOneGlobal (globalDbarClosedForm E M a ha) = a := by
  apply Subtype.ext
  exact Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.toGlobal_onOpen a.val

theorem closedDbarOneGlobal_injective :
    Function.Injective (GlobalDolbeaultForms.closedDbarOneGlobal (E := E) (M := M)) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  have H := congrArg (fun f : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M 0 1 =>
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ f.val) h
  simpa only [GlobalDolbeaultForms.closedDbarOneGlobal_onTop] using H

theorem globalZeroFormOnTop_toGlobal (s : AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E (⊤ : Opens M) 0) :
    GlobalDolbeaultForms.globalZeroFormOnTop (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal s.val) = s := by
  apply Subtype.ext
  exact Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.onOpen_toGlobal s.val

theorem closedDbarOneGlobal_derivative (s : AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E (⊤ : Opens M) 0) :
    GlobalDolbeaultForms.closedDbarOneGlobal (DolbeaultBoundary.globalDbarDerivative E M s) =
      Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (GlobalDolbeaultForms.globalZeroPureForm
        (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal s.val)) := by
  apply Subtype.ext
  apply (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onTopEquiv (E := E) (M := M)).injective
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ (GlobalDolbeaultForms.closedDbarOneGlobal
      (DolbeaultBoundary.globalDbarDerivative E M s)).val =
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime
      (GlobalDolbeaultForms.globalZeroPureForm (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal s.val))).val
  rw [GlobalDolbeaultForms.closedDbarOneGlobal_onTop]
  have H := GlobalDolbeaultForms.globalZeroFormOnTop_dbar (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal s.val)
  rw [globalZeroFormOnTop_toGlobal] at H
  exact H

theorem closedType01ToDbarForm_injective :
    Function.Injective (closedType01ToDbarForm E M) := by
  intro a b h
  apply Subtype.ext
  have H := congrArg (GlobalDolbeaultForms.closedDbarOneGlobal (E := E) (M := M)) h
  change GlobalDolbeaultForms.closedDbarOneGlobal (globalDbarClosedForm E M a.val
      (pureOne_dbar_zero_of_d_zero E M a.val a.property)) =
    GlobalDolbeaultForms.closedDbarOneGlobal (globalDbarClosedForm E M b.val
      (pureOne_dbar_zero_of_d_zero E M b.val b.property)) at H
  simpa only [closedDbarOneGlobal_global] using H

end

end OAI.RepresentationTheory.Theta.Geometric.ClosedPureDolbeaultMap
