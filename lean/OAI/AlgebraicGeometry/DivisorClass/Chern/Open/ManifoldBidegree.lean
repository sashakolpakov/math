import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldAction
import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.DolbeaultPrime

/-! # Manifold Bidegree -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldBidegree

noncomputable section

/-! The original chart-character condition on open manifold forms. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {n p q : ℕ} {U V : Opens M}

def OpenManifoldHasBidegree (p q : ℕ) (form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) : Prop :=
  ∀ e ∈ atlas E M, ∀ y ∈ Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain e (U : Set M),
    ∀ (z : ℂˣ) (v : Fin n → E),
      form.extension.inChart e y (fun i => (z : ℂ) • v i) =
        Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z * form.extension.inChart e y v

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem openManifold_restrict_inChart (h : V ≤ U)
    (form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n)
    (e : OpenPartialHomeomorph M E) {y : E} (hy : e.symm y ∈ V) :
    (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h form).extension.inChart e y =
      form.extension.inChart e y := by
  unfold Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply _ ⟨e.symm y, hy⟩,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply form ⟨e.symm y, h hy⟩]
  rfl

omit [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem openManifoldHasBidegree_restrict (h : V ≤ U)
    {form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n} (hf : OpenManifoldHasBidegree p q form) :
    OpenManifoldHasBidegree p q (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h form) := by
  intro e he y hy z v
  rw [openManifold_restrict_inChart h form e hy.2]
  exact hf e he y ⟨hy.1, h hy.2⟩ z v

def antiOpenManifoldFormSubmodule (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] (U : Opens M) (q : ℕ) :
    Submodule ℂ (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U q) where
  carrier := OpenManifoldHasBidegree 0 q
  zero_mem' := by
    intro e he y hy z v
    have hz : (0 : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U q).extension = 0 :=
      Analysis.DifferentialForms.Manifold.Open.openManifoldFormExtension_zero U
    rw [hz, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_zero]
    simp
  add_mem' := by
    intro f g hf hg e he y hy z v
    simp only [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_add, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add,
      Pi.add_apply, ContinuousAlternatingMap.add_apply]
    rw [hf e he y hy z v, hg e he y hy z v, mul_add]
  smul_mem' := by
    intro c f hf e he y hy z v
    simp only [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_smul, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul,
      Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    rw [hf e he y hy z v]
    ring

abbrev AntiOpenManifoldForm (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] (U : Opens M) (q : ℕ) :=
  ↥(antiOpenManifoldFormSubmodule E U q)

instance antiOpenManifoldFormAddCommGroup (U : Opens M) (q : ℕ) :
    AddCommGroup (AntiOpenManifoldForm E U q) := Module.addCommMonoidToAddCommGroup ℂ

def antiOpenManifoldFormRestrict (h : V ≤ U) :
    AntiOpenManifoldForm E U q →ₗ[ℂ] AntiOpenManifoldForm E V q where
  toFun f := ⟨Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h f.1, openManifoldHasBidegree_restrict h f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem openManifoldHasBidegree_toChartOn
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (W : Opens E) (hW : W ≤ Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e)
    {form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen e W) n}
    (hf : OpenManifoldHasBidegree p q form) :
    DolbeaultPrime.OpenFormHasBidegree p q (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toChartOn e he W hW form) :=
  fun y z v => hf e he y ⟨hW y.property, Analysis.DifferentialForms.Manifold.ChartEquiv.mem_chartPreimageOpen_symm e W hW y.property⟩ z v

theorem openManifoldHasBidegree_fromChartOn
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (W : Opens E) (hW : W ≤ Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e)
    {form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm W n} (hn : n = p + q) (hf : DolbeaultPrime.OpenFormHasBidegree p q form) :
    OpenManifoldHasBidegree p q (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.fromChartOn e he W form) := by
  subst n
  let a := Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.fromChartOn e he W form
  intro f hfAtlas y hy
  apply a.extension.hasBidegree_inChart_of_transition f e hfAtlas he hy.1 hy.2.1
  have hyW : e (f.symm y) ∈ W := hy.2.2
  have hid := congrArg (fun b : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm W (p + q) => b ⟨e (f.symm y), hyW⟩)
    (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toChartOn_fromChartOn e he W hW form)
  change a.extension.inChart e (e (f.symm y)) = form ⟨e (f.symm y), hyW⟩ at hid
  rw [hid]
  exact hf ⟨e (f.symm y), hyW⟩

omit [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem openManifoldHasBidegree_onOpen
    {form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (p + q)}
    (hf : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M p q (form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q))) (U : Opens M) :
    OpenManifoldHasBidegree p q (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U form) := by
  intro e he y hy
  have hid : (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U form).extension.inChart e y =
      (form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q)).inChart e y := by
    unfold Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
    rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply _ ⟨e.symm y, hy.2⟩]
    rfl
  rw [hid]
  exact hf e he y hy.1

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldBidegree
