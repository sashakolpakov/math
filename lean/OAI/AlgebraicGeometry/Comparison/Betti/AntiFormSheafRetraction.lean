import OAI.AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf
import OAI.AlgebraicGeometry.Comparison.Betti.Open.ChartEvaluation

/-! # Anti Form Sheaf Retraction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AntiFormSheafRetraction.Dolbeault

noncomputable section

/-! The original antiholomorphic form sheaf is a direct summand of the
actual smooth form sheaf, via its proved bidegree projector. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf OAI.AlgebraicGeometry.Comparison.Betti.Open.ChartEvaluation.Hodge

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

def antiOpenFormProjection (U : Opens M) (q : ℕ) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U q →ₗ[ℂ] DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E U q :=
  (Open.FiltrationDescent.Hodge.openTypeProjection U q ⟨(0, q), Nat.zero_add q⟩).codRestrict _ (fun a =>
    (Open.ChartEvaluation.Hodge.mem_openPureFormsInDegree_iff U q ⟨(0, q), Nat.zero_add q⟩ _).mp
      (Open.ChartEvaluation.Hodge.openTypeProjection_pure U q ⟨(0, q), Nat.zero_add q⟩ a))

theorem antiOpenFormProjection_identity (U : Opens M) (q : ℕ) (a : DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E U q) :
    antiOpenFormProjection E M U q a.val = a :=
  Subtype.ext (Open.ChartEvaluation.Hodge.openTypeProjection_identity U q ⟨(0, q), Nat.zero_add q⟩ a.val
    ((Open.ChartEvaluation.Hodge.mem_openPureFormsInDegree_iff U q ⟨(0, q), Nat.zero_add q⟩ a.val).mpr a.property))

def antiFormSheafInclusion (q : ℕ) : DivisorClass.Chern.PureManifoldDolbeaultSheaf.antiOpenManifoldFormSheaf E M q ⟶ Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M q :=
  ObjectProperty.homMk {
    app U := ModuleCat.ofHom (DivisorClass.Chern.Open.ManifoldBidegree.antiOpenManifoldFormSubmodule E U.unop q).subtype
    naturality := by
      intro U V f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      rfl }

def antiFormSheafRetraction (q : ℕ) : Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M q ⟶ DivisorClass.Chern.PureManifoldDolbeaultSheaf.antiOpenManifoldFormSheaf E M q :=
  ObjectProperty.homMk {
    app U := ModuleCat.ofHom (antiOpenFormProjection E M U.unop q)
    naturality := by
      intro U V f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact Subtype.ext (Open.FiltrationDescent.Hodge.openTypeProjection_restrict (leOfHom f.unop) q ⟨(0, q), Nat.zero_add q⟩ a).symm }

theorem antiFormSheafInclusion_retraction (q : ℕ) :
    antiFormSheafInclusion E M q ≫ antiFormSheafRetraction E M q = 𝟙 _ := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact antiOpenFormProjection_identity E M U.unop q a

end

end OAI.AlgebraicGeometry.Comparison.Betti.AntiFormSheafRetraction.Dolbeault
