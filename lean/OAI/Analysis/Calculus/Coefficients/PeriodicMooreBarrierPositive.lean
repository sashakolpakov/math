import OAI.Analysis.PDE.Dirichlet.PositiveOpen
import OAI.Analysis.Calculus.Coefficients.Cofactor
import Mathlib.Topology.ContinuousMap.Bounded.Basic

open Set Filter Module Metric
open scoped Topology BoundedContinuousFunction Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.Calculus.Coefficients

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

/-- Uniform convergence of Hermitian matrix fields on a compact set
preserves strict positivity after finitely many terms. -/
theorem eventually_positive_of_compact_uniform_limit
    {X : Type*} [TopologicalSpace X] {n : ℕ} {K : Set X} (hK : IsCompact K)
    (A : ℕ → X → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (B : X → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : ∀ j, ContinuousOn (A j) K) (hB : ContinuousOn B K)
    (hHerm : ∀ j x, x ∈ K → (A j x).IsHermitian)
    (hpos : ∀ x, x ∈ K → (OAI.LinearAlgebra.Moore.complexify (B x)).PosDef)
    (hc : TendstoUniformlyOn A B atTop K) :
    ∀ᶠ j in atTop, ∀ x, x ∈ K → (OAI.LinearAlgebra.Moore.complexify (A j x)).PosDef := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : CompactSpace (sphere (0 : Fin n → Quaternion ℝ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let a : ℕ → K →ᵇ Matrix (Fin n) (Fin n) (Quaternion ℝ) :=
    fun j ↦ BoundedContinuousFunction.mkOfCompact ⟨_, (hA j).domRestrict⟩
  let b : K →ᵇ Matrix (Fin n) (Fin n) (Quaternion ℝ) :=
    BoundedContinuousFunction.mkOfCompact ⟨_, hB.domRestrict⟩
  have hab : Tendsto a atTop (𝓝 b) := by
    apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hc ε hε] with j hj
    intro x
    exact hj x x.property
  let q : (K →ᵇ Matrix (Fin n) (Fin n) (Quaternion ℝ)) →
      (K × sphere (0 : Fin n → Quaternion ℝ) 1) → ℝ :=
    fun f p ↦ (OAI.Analysis.PDE.Dirichlet.quaternionForm (f p.1) p.2).re
  have hq : Continuous (fun p : (K →ᵇ Matrix (Fin n) (Fin n) (Quaternion ℝ)) ×
      (K × sphere (0 : Fin n → Quaternion ℝ) 1) ↦ q p.1 p.2) := by
    have heval : Continuous (fun p : (K →ᵇ Matrix (Fin n) (Fin n) (Quaternion ℝ)) ×
        (K × sphere (0 : Fin n → Quaternion ℝ) 1) ↦ p.1 p.2.1) :=
      continuous_eval.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    exact OAI.Analysis.PDE.Dirichlet.continuous_quaternionForm_re heval (by fun_prop)
  have hopen := OAI.Analysis.PDE.Dirichlet.isOpen_positive_compact_family q hq
  have hb : b ∈ {z | ∀ p, 0 < q z p} := by
    intro p
    exact (OAI.Analysis.PDE.Dirichlet.complexify_posDef_iff_unit_sphere _
      (OAI.LinearAlgebra.Moore.isHermitian_of_complexify (hpos p.1 p.1.property).isHermitian)).mp
        (hpos p.1 p.1.property) p.2 p.2.property
  filter_upwards [hab (hopen.mem_nhds hb)] with j hj
  intro x hx
  apply (OAI.Analysis.PDE.Dirichlet.complexify_posDef_iff_unit_sphere _ (hHerm j x hx)).mpr
  intro z hz
  exact hj (⟨x, hx⟩, ⟨z, hz⟩)

end OAI.Analysis.Calculus.Coefficients
