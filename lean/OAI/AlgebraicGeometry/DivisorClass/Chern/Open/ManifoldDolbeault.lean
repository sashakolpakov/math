import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldBidegree
import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldDolbeault

/-! # Manifold Dolbeault -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldDolbeault

noncomputable section

section

/-! The original Dolbeault projection on genuine open manifold sections. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicTopology.DeRham.Comparison.ManifoldDolbeault
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {n p q : ℕ} {U V : Opens M}

def openManifoldDolbeaultD (p q n : ℕ) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U (n + 1) :=
  (1 / 2 : ℂ) • ((Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (E := E) (U := U) (n := n)) + (-(AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultPrimeCharacter p q)⁻¹) •
    (ManifoldAction.openManifoldComplexAction AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹).comp Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d)

theorem openManifoldDolbeaultD_apply (p q : ℕ) (form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :
    openManifoldDolbeaultD p q n form = (1 / 2 : ℂ) • (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d form +
      (-(AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultPrimeCharacter p q)⁻¹) •
        ManifoldAction.openManifoldComplexAction AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹ (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d form)) := rfl

theorem openManifoldDolbeaultD_restrict (h : V ≤ U)
    (form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h (openManifoldDolbeaultD p q n form) =
      openManifoldDolbeaultD p q n (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h form) := by
  simp only [openManifoldDolbeaultD_apply, map_smul, map_add,
    ManifoldAction.openManifoldComplexAction_restrict, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_d]

theorem openManifoldDolbeaultD_inChart (p q : ℕ)
    (form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E}
    (hy : y ∈ Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain e (U : Set M)) :
    (openManifoldDolbeaultD p q n form).extension.inChart e y = (1 / 2 : ℂ) •
      (extDeriv (form.extension.inChart e) y - (AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultPrimeCharacter p q)⁻¹ •
        Analysis.DifferentialForms.Manifold.Bidegree.scalarCovectorPullback E (n + 1) Complex.I (extDeriv (form.extension.inChart e) y)) := by
  rw [openManifoldDolbeaultD_apply, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_smul,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_add, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_smul,
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul]
  simp only [Pi.smul_apply, Pi.add_apply, ManifoldAction.openManifoldComplexAction_inChart _ _ e he hy,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d_inChart form e he hy, inv_inv, AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit_coe]
  ext v
  change (1 / 2 : ℂ) * (extDeriv (form.extension.inChart e) y v +
    (-(AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultPrimeCharacter p q)⁻¹) *
      extDeriv (form.extension.inChart e) y (fun i => Complex.I • v i)) =
    (1 / 2 : ℂ) * (extDeriv (form.extension.inChart e) y v -
      (AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultPrimeCharacter p q)⁻¹ *
        extDeriv (form.extension.inChart e) y (fun i => Complex.I • v i))
  ring

theorem openManifoldDolbeaultD_eq_local {form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n}
    (hn : n = p + q) (hf : ManifoldBidegree.OpenManifoldHasBidegree p q form)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E}
    (hy : y ∈ Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain e (U : Set M)) :
    (openManifoldDolbeaultD p q n form).extension.inChart e y =
      Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime (form.extension.inChart e) y := by
  subst n
  rw [openManifoldDolbeaultD_inChart p q form e he hy]
  have hdiff : DifferentiableAt ℝ (form.extension.inChart e) y :=
    ((form.smooth e he).contDiffAt
      ((e.isOpen_inter_preimage_symm U.isOpen).mem_nhds hy)).differentiableAt (by simp)
  have hpure : ∀ᶠ t in 𝓝 y, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p q (form.extension.inChart e t) := by
    filter_upwards [(e.isOpen_inter_preimage_symm U.isOpen).mem_nhds hy] with t ht
    exact hf e he t ht
  rw [← Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivPrime_add_extDerivDoublePrime (form.extension.inChart e) y]
  apply AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultDoublePrimeProjection_of_characters
  · ext v
    exact Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivPrime_bidegree_character hdiff hpure AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit v
  · ext v
    exact Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime_bidegree_character hdiff hpure AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit v

theorem openManifoldDolbeaultD_hasBidegree {form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n}
    (hn : n = p + q) (hf : ManifoldBidegree.OpenManifoldHasBidegree p q form) :
    ManifoldBidegree.OpenManifoldHasBidegree p (q + 1) (openManifoldDolbeaultD p q n form) := by
  subst n
  intro e he y hy z v
  rw [openManifoldDolbeaultD_eq_local rfl hf e he hy]
  apply Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime_bidegree_character
    (((form.smooth e he).contDiffAt
      ((e.isOpen_inter_preimage_symm U.isOpen).mem_nhds hy)).differentiableAt (by simp))
  filter_upwards [(e.isOpen_inter_preimage_symm U.isOpen).mem_nhds hy] with t ht
  exact hf e he t ht

theorem openManifoldDolbeaultD_onOpen (U : Opens M) (form : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q) :
    openManifoldDolbeaultD p q (p + q) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U form.1) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U (AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.manifoldDolbeaultDoublePrimeForm E M p q form) := by
  rw [openManifoldDolbeaultD_apply, AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.manifoldDolbeaultDoublePrimeForm_apply]
  simp only [map_smul, map_sub, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen_d]
  rw [ManifoldAction.openManifoldComplexAction_onOpen]
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  ext v
  change (1 / 2 : ℂ) * (_ + (-_) * _) = (1 / 2 : ℂ) * (_ - _ * _)
  ring

end

/-! The complementary genuine Dolbeault differential on open manifold sections. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {n p q : ℕ} {U : Opens M}

def openManifoldDolbeaultPrime (p q n : ℕ) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U (n + 1) :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d + (-1 : ℂ) • openManifoldDolbeaultD p q n

theorem openManifoldDolbeaultPrime_add_dbar (p q : ℕ) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :
    openManifoldDolbeaultPrime p q n a + openManifoldDolbeaultD p q n a =
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  ext v
  change (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a x v + (-1 : ℂ) * _) + _ = _
  ring

theorem openManifoldDolbeaultPrime_eq_local {a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n}
    (hn : n = p + q) (ha : ManifoldBidegree.OpenManifoldHasBidegree p q a)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E}
    (hy : y ∈ Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain e (U : Set M)) :
    (openManifoldDolbeaultPrime p q n a).extension.inChart e y =
      Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivPrime (a.extension.inChart e) y := by
  have hs := congrArg (fun b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U (n + 1) => b.extension.inChart e y)
    (openManifoldDolbeaultPrime_add_dbar p q a)
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_add, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add] at hs
  change (openManifoldDolbeaultPrime p q n a).extension.inChart e y +
    (openManifoldDolbeaultD p q n a).extension.inChart e y = _ at hs
  rw [openManifoldDolbeaultD_eq_local hn ha e he hy,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d_inChart a e he hy] at hs
  exact add_right_cancel (hs.trans (Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivPrime_add_extDerivDoublePrime (a.extension.inChart e) y).symm)

theorem openManifoldDolbeaultPrime_hasBidegree {a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n}
    (hn : n = p + q) (ha : ManifoldBidegree.OpenManifoldHasBidegree p q a) :
    ManifoldBidegree.OpenManifoldHasBidegree (p + 1) q (openManifoldDolbeaultPrime p q n a) := by
  subst n
  intro e he y hy z v
  rw [openManifoldDolbeaultPrime_eq_local rfl ha e he hy]
  apply Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivPrime_bidegree_character
    (((a.smooth e he).contDiffAt
      ((e.isOpen_inter_preimage_symm U.isOpen).mem_nhds hy)).differentiableAt (by simp))
  filter_upwards [(e.isOpen_inter_preimage_symm U.isOpen).mem_nhds hy] with t ht
  exact ha e he t ht

omit [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem openManifoldHasBidegree_add {a b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n}
    (ha : ManifoldBidegree.OpenManifoldHasBidegree p q a) (hb : ManifoldBidegree.OpenManifoldHasBidegree p q b) :
    ManifoldBidegree.OpenManifoldHasBidegree p q (a + b) := by
  intro e he y hy z v
  simp only [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_add, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add,
    Pi.add_apply, ContinuousAlternatingMap.add_apply]
  rw [ha e he y hy z v, hb e he y hy z v, mul_add]

omit [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem openManifoldHasBidegree_smul (c : ℂ) {a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n}
    (ha : ManifoldBidegree.OpenManifoldHasBidegree p q a) : ManifoldBidegree.OpenManifoldHasBidegree p q (c • a) := by
  intro e he y hy z v
  simp only [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_smul, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul,
    Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [ha e he y hy z v]
  ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldDolbeault
