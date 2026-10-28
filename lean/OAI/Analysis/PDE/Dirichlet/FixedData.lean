import OAI.Analysis.PDE.Dirichlet.Continuity
import OAI.Analysis.PDE.Dirichlet.RigidBounds

open Set Filter
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

private theorem continuous_complex_pair {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x ↦ (⟨f x, g x⟩ : ℂ)) := by
  have heq : (fun x ↦ (⟨f x, g x⟩ : ℂ)) =
      (fun x ↦ (f x : ℂ) + (g x : ℂ) * Complex.I) := by
    funext x
    apply Complex.ext <;> simp
  rw [heq]
  exact (Complex.continuous_ofReal.comp hf).add
    ((Complex.continuous_ofReal.comp hg).mul continuous_const)

theorem continuous_complexify_map {X : Type*} [TopologicalSpace X] {n : ℕ}
    {A : X → Matrix (Fin n) (Fin n) (Quaternion ℝ)} (hA : Continuous A) :
    Continuous (fun x ↦ OAI.LinearAlgebra.Moore.complexify (A x)) := by
  apply continuous_pi
  rintro ⟨i, α⟩
  apply continuous_pi
  rintro ⟨j, β⟩
  have ha : Continuous (fun x ↦ A x i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp hA)
  fin_cases α <;> fin_cases β
  · exact continuous_complex_pair (Quaternion.continuous_re.comp ha) (Quaternion.continuous_imI.comp ha)
  · exact continuous_complex_pair (Quaternion.continuous_imJ.comp ha) (Quaternion.continuous_imK.comp ha)
  · exact continuous_complex_pair (Quaternion.continuous_imJ.comp ha).neg (Quaternion.continuous_imK.comp ha)
  · exact continuous_complex_pair (Quaternion.continuous_re.comp ha) (Quaternion.continuous_imI.comp ha).neg

/-- The operator norm controls both signs of a Hermitian quaternionic matrix. -/
theorem complexify_shift_posSemidef {n : ℕ} (D : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hD : D.IsHermitian) {K : ℝ} (hK : ‖OAI.LinearAlgebra.Moore.complexify D‖ ≤ K) :
    (OAI.LinearAlgebra.Moore.complexify (D + K • (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)))).PosSemidef ∧
    (OAI.LinearAlgebra.Moore.complexify (-D + K • (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)))).PosSemidef := by
  have hself : IsSelfAdjoint (OAI.LinearAlgebra.Moore.complexify D) := OAI.LinearAlgebra.Moore.complexify_isHermitian hD
  have hupper : OAI.LinearAlgebra.Moore.complexify D ≤ ‖OAI.LinearAlgebra.Moore.complexify D‖ • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using hself.le_algebraMap_norm_self
  have hlower : -(‖OAI.LinearAlgebra.Moore.complexify D‖ • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ)) ≤ OAI.LinearAlgebra.Moore.complexify D := by
    simpa only [Algebra.algebraMap_eq_smul_one] using hself.neg_algebraMap_norm_le_self
  have hm : ‖OAI.LinearAlgebra.Moore.complexify D‖ • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) ≤ K • 1 :=
    smul_le_smul_of_nonneg_right hK (Matrix.PosSemidef.one.nonneg)
  have hneg : OAI.LinearAlgebra.Moore.complexify (-D) = -OAI.LinearAlgebra.Moore.complexify D := by
    simpa only [neg_one_smul] using OAI.LinearAlgebra.Moore.complexify_real_smul (-1 : ℝ) D
  constructor
  · apply Matrix.nonneg_iff_posSemidef.mp
    rw [OAI.LinearAlgebra.Moore.complexify_add, OAI.LinearAlgebra.Moore.complexify_real_smul, OAI.LinearAlgebra.Moore.complexify_one]
    have h := sub_nonneg.mpr ((neg_le_neg hm).trans hlower)
    simpa only [sub_neg_eq_add] using h
  · apply Matrix.nonneg_iff_posSemidef.mp
    rw [OAI.LinearAlgebra.Moore.complexify_add, hneg, OAI.LinearAlgebra.Moore.complexify_real_smul, OAI.LinearAlgebra.Moore.complexify_one]
    have h := sub_nonneg.mpr (hupper.trans hm)
    simpa only [sub_eq_add_neg, add_comm] using h

/-- Uniform two-sided Hessian domination for fixed smooth data on a compact
set. The constant is obtained from the actual Hessian, not assumed. -/
theorem exists_fixed_hessian_bound {n : ℕ} {f : CoordinateSpace n 4 → ℝ}
    (hf : ContDiff ℝ 2 f) {S : Set (CoordinateSpace n 4)} (hS : IsCompact S) :
    ∃ K : ℝ, 0 < K ∧ ∀ x ∈ S,
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x +
        K • (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)))).PosSemidef ∧
      (OAI.LinearAlgebra.Moore.complexify (-quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x +
        K • (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)))).PosSemidef := by
  have hc : Continuous (fun x ↦ ‖OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)‖) :=
    (continuous_complexify_map (continuous_quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots hf)).norm
  obtain ⟨C, hC⟩ := hS.bddAbove_image hc.continuousOn
  refine ⟨max C 0 + 1, by positivity, ?_⟩
  intro x hx
  apply complexify_shift_posSemidef _ (quaternionHessian_isHermitian OAI.Analysis.Calculus.Quaternion.fourSlots hf.contDiffAt)
  have h := hC (mem_image_of_mem _ hx)
  have hmax : C ≤ max C 0 := le_max_left _ _
  linarith

/-- A single forcing constant works for every solution with the fixed
background, right-hand side, and positive trace lower bound. -/
theorem exists_uniform_rigid_forcing {n : ℕ} {B₀ F : CoordinateSpace n 4 → ℝ}
    (hB₀ : ContDiff ℝ 3 B₀) (hF : ContDiff ℝ 1 F)
    (e : CoordinateSpace n 4) (R : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hR : Rᴴ = -R) {S : Set (CoordinateSpace n 4)} (hS : IsCompact S)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : CoordinateSpace n 4 → ℝ, ContDiff ℝ 3 u →
      ∀ x ∈ S,
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z ↦ B₀ z + u z) x)).PosDef →
      κ ≤ OAI.LinearAlgebra.Moore.mooreDifferential n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z ↦ B₀ z + u z) x) 1 →
      (fun y ↦ OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z ↦ B₀ z + u z) y)) =ᶠ[𝓝 x] F →
      |mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z ↦ B₀ z + u z))
        (affineDerivative u e (realMatrixAction (realRepresentation R))) x| ≤
        C * OAI.LinearAlgebra.Moore.mooreDifferential n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z ↦ B₀ z + u z) x) 1 := by
  have hXB : ContDiff ℝ 2 (affineDerivative B₀ e (realMatrixAction (realRepresentation R))) :=
    contDiff_affineDerivative hB₀ (by norm_num) _ _
  obtain ⟨K, hK, hKH⟩ := exists_fixed_hessian_bound hXB hS
  have hXF : ContDiff ℝ 0 (affineDerivative F e (realMatrixAction (realRepresentation R))) :=
    contDiff_affineDerivative hF (by norm_num) _ _
  obtain ⟨L₀, hL₀⟩ := hS.bddAbove_image hXF.continuous.abs.continuousOn
  let L := max L₀ 0 + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hLF : ∀ x ∈ S, |affineDerivative F e (realMatrixAction (realRepresentation R)) x| ≤ L := by
    intro x hx
    have h := hL₀ (mem_image_of_mem _ hx)
    have hm : L₀ ≤ max L₀ 0 := le_max_left _ _
    dsimp [L]
    linarith
  refine ⟨L / κ + K, by positivity, ?_⟩
  intro u hu x hx hA htrace heq
  obtain ⟨hp, hm⟩ := hKH x hx
  exact mooreLinearization_rigid_forcing hB₀ hu e R hR
    ((hF.differentiable (by norm_num)) x) heq hκ hL.le hA htrace (hLF x hx) hp
    (by simpa only [neg_one_smul] using hm)

end OAI.Analysis.PDE.Dirichlet
