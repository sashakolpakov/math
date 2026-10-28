import OAI.Analysis.PDE.Dirichlet.C2HolderHermitian
import OAI.Analysis.PDE.Dirichlet.Coercivity
import OAI.Analysis.PDE.Dirichlet.NormalBounded
import Mathlib.Topology.Maps.Proper.Basic

open Set Metric
open scoped Matrix Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.Normed.Function.Holder

theorem isOpen_positive_compact_family {Z P : Type*} [TopologicalSpace Z]
    [TopologicalSpace P] [CompactSpace P] (q : Z → P → ℝ)
    (hq : Continuous (fun p : Z × P ↦ q p.1 p.2)) :
    IsOpen {z | ∀ p, 0 < q z p} := by
  classical
  have hc : IsClosed (Prod.fst '' {p : Z × P | q p.1 p.2 ≤ 0}) :=
    isClosedMap_fst_of_compactSpace _ (isClosed_le hq continuous_const)
  have he : {z | ∀ p, 0 < q z p} =
      (Prod.fst '' {p : Z × P | q p.1 p.2 ≤ 0})ᶜ := by
    ext z
    change (∀ p, 0 < q z p) ↔ ¬ z ∈ Prod.fst '' {p : Z × P | q p.1 p.2 ≤ 0}
    constructor
    · intro hz ⟨⟨z', p⟩, hp, heq⟩
      change z' = z at heq
      subst z'
      exact (not_le_of_gt (hz p)) hp
    · intro hz p
      apply lt_of_not_ge
      intro hp
      exact hz ⟨(z, p), hp, rfl⟩
  rw [he]
  exact hc.isOpen_compl

theorem complexify_posDef_iff_unit_sphere {n : ℕ}
    (A : Matrix (Fin n) (Fin n) Q) (hA : A.IsHermitian) :
    (OAI.LinearAlgebra.Moore.complexify A).PosDef ↔
      ∀ z ∈ sphere (0 : Fin n → Q) 1, 0 < (quaternionForm A z).re := by
  rw [OAI.LinearAlgebra.Moore.complexify_posDef_iff hA]
  constructor
  · intro h z hz
    apply h z
    intro hzero
    simp [hzero] at hz
  · intro h z hz
    let u : Fin n → Q := ‖z‖⁻¹ • z
    have hu : ‖u‖ = 1 := by simp [u, norm_smul, norm_ne_zero_iff.mpr hz]
    have hzu : ‖z‖ • u = z := by simp [u, smul_smul, norm_ne_zero_iff.mpr hz]
    have hpos : 0 < (quaternionForm A u).re := h u (by simpa [mem_sphere, dist_zero_right] using hu)
    have hs := congrArg (fun q : Q ↦ q.re) (quaternionForm_smul_vector A ‖z‖ u)
    rw [hzu] at hs
    change (quaternionForm A z).re = ‖z‖ ^ 2 * (quaternionForm A u).re at hs
    rw [hs]
    exact mul_pos (pow_pos (norm_pos_iff.mpr hz) 2) hpos

/-- Strict quaternionic Hessian positivity is open in the actual C²,α
norm on every compact part of the closed domain. For periodic problems
the compact set can be chosen to be a fundamental cell. -/
theorem isOpen_positive_hessian_on_compact {n : ℕ}
    {Ω K S : Set (CoordinateSpace n 4)} {hΩK : Ω ⊆ K} {α : ℝ}
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ closure Ω) (hS : IsCompact S) (hSK : S ⊆ K) :
    IsOpen {f : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α | ∀ x : S,
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots f)
        ⟨x, hSK x.property⟩)).PosDef} := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let : CompactSpace (sphere (0 : Fin n → Q) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let J := (OAI.Analysis.Normed.Function.Holder.HolderMap.valueCLM (X := K) (F := Matrix (Fin n) (Fin n) Q) (α := α)).comp
    (quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots)
  let q : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α → (S × sphere (0 : Fin n → Q) 1) → ℝ :=
    fun f p ↦ (quaternionForm (J f ⟨p.1, hSK p.1.property⟩) p.2).re
  have hq : Continuous (fun p : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α ×
      (S × sphere (0 : Fin n → Q) 1) ↦ q p.1 p.2) := by
    have hJ : Continuous (fun p : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α ×
        (S × sphere (0 : Fin n → Q) 1) ↦ J p.1 ⟨p.2.1, hSK p.2.1.property⟩) :=
      continuous_eval.comp ((J.continuous.comp continuous_fst).prodMk (by fun_prop))
    exact continuous_quaternionForm_re hJ (by fun_prop)
  have hopen := isOpen_positive_compact_family q hq
  have he : {f : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α | ∀ x : S,
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots f)
        ⟨x, hSK x.property⟩)).PosDef} = {f | ∀ p, 0 < q f p} := by
    ext f
    constructor
    · intro hf p
      exact (complexify_posDef_iff_unit_sphere _
        (quaternionHessianField_isHermitian hΩ hKΩ OAI.Analysis.Calculus.Quaternion.fourSlots f _)).mp (hf p.1)
          p.2 p.2.property
    · intro hf x
      apply (complexify_posDef_iff_unit_sphere _
        (quaternionHessianField_isHermitian hΩ hKΩ OAI.Analysis.Calculus.Quaternion.fourSlots f _)).mpr
      intro z hz
      exact hf (x, ⟨z, hz⟩)
  rw [he]
  exact hopen

end OAI.Analysis.PDE.Dirichlet
