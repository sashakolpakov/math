import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldDolbeaultIdentities
import OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham

/-! # De Rham Complex -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DeRhamComplex

noncomputable section

section

/-! The holomorphic de Rham complex is defined independently as the kernel of the actual antiholomorphic differential. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

def forms (n : ℕ) : Submodule ℂ (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M n 0) :=
  LinearMap.ker Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime

def differential (n : ℕ) : forms E M n →ₗ[ℂ] forms E M (n + 1) :=
  (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime.comp (forms E M n).subtype).codRestrict _ (by
    intro a
    change Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime a.val) = 0
    have h := Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime_dPrime_add_dPrime_dDoublePrime a.val
    have ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime a.val = 0 := a.property
    rw [ha, map_zero, add_zero] at h
    exact h)

theorem differential_squared (n : ℕ) (a : forms E M n) :
    differential E M (n + 1) (differential E M n a) = 0 := by
  apply Subtype.ext
  exact Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime_squared a.val

def complex : CochainComplex (ModuleCat.{0} ℂ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℂ (forms E M n))
    (fun n => ModuleCat.ofHom (differential E M n)) (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact differential_squared E M n a)

theorem complex_d (n : ℕ) :
    (complex E M).d n (n + 1) = ModuleCat.ofHom (differential E M n) :=
  CochainComplex.of_d (fun k => ModuleCat.of ℂ (forms E M k))
    (fun k => ModuleCat.ofHom (differential E M k)) n

def inclusion (n : ℕ) : forms E M n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n :=
  (Analysis.DifferentialForms.Manifold.ManifoldBidegree.pureManifoldFormSubmodule E M n 0).subtype.comp (forms E M n).subtype

theorem inclusion_differential (n : ℕ) (a : forms E M n) :
    inclusion E M (n + 1) (differential E M n a) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (inclusion E M n a) := by
  have h := Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime_add_dDoublePrime a.val
  have ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime a.val = 0 := a.property
  rw [ha] at h
  simp only [ZeroMemClass.coe_zero, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_self, add_zero] at h
  exact h

def inclusionCochainMap : complex E M ⟶ Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (inclusion E M n)) (fun n => by
    rw [Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex_d]
    change ModuleCat.ofHom (inclusion E M n) ≫ ModuleCat.ofHom Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d =
      (complex E M).d n (n + 1) ≫ ModuleCat.ofHom (inclusion E M (n + 1))
    rw [complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (inclusion_differential E M n a).symm)

end

/-! A pure (n,0)-form is holomorphic exactly when its derivative has type (n+1,0). -/

open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem derivative_pure (n : ℕ) (a : forms E M n) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M (n + 1) 0 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (inclusion E M n a)).val := by
  rw [← inclusion_differential]
  exact (differential E M n a).val.hasManifoldBidegree

theorem dDoublePrime_zero_of_derivative_pure (n : ℕ) (a : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M n 0)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M (n + 1) 0 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a.val).val) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime a = 0 := by
  have hc : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction (AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a.val) =
      AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultPrimeCharacter n 0 • Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a.val := by
    apply Subtype.ext
    change Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction (AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a.val).val =
      AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultPrimeCharacter n 0 • (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a.val).val
    simpa only [inv_inv, AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultPrimeCharacter] using ha.complexAction_eq (AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹)
  have hz : AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.manifoldDolbeaultDoublePrimeForm E M n 0 a = 0 := by
    rw [AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.manifoldDolbeaultDoublePrimeForm_apply, hc, smul_smul,
      inv_mul_cancel₀ (AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultPrimeCharacter_ne_zero n 0), one_smul, sub_self, smul_zero]
  apply Subtype.ext
  rw [Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime_coe, hz]
  rfl

theorem mem_forms_iff_derivative_pure (n : ℕ) (a : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M n 0) :
    a ∈ forms E M n ↔
      Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M (n + 1) 0 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a.val).val := by
  constructor
  · intro ha
    exact derivative_pure n ⟨a, ha⟩
  · exact dDoublePrime_zero_of_derivative_pure n a

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DeRhamComplex
