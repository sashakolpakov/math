import OAI.Analysis.PDE.Dirichlet.ComparisonLocal
import OAI.Analysis.PDE.Dirichlet.Linearized

open Set Filter
open scoped Topology Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem mooreLinearization_congr_germ {n : ℕ}
    (A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    {f g : CoordinateSpace n 4 → ℝ} {x : CoordinateSpace n 4}
    (h : f =ᶠ[𝓝 x] g) : mooreLinearization A f x = mooreLinearization A g x := by
  simp only [mooreLinearization, quaternionHessian_congr_germ OAI.Analysis.Calculus.Quaternion.fourSlots h]

theorem mooreLinearization_add_smul_at {n : ℕ}
    (A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    {f g : CoordinateSpace n 4 → ℝ} {x : CoordinateSpace n 4}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (c : ℝ) :
    mooreLinearization A (fun y ↦ f y + c • g y) x =
      mooreLinearization A f x + c * mooreLinearization A g x := by
  obtain ⟨f', hf', hfeq⟩ := exists_contDiff_extension_near_point hf
  obtain ⟨g', hg', hgeq⟩ := exists_contDiff_extension_near_point hg
  have heq : (fun y ↦ f' y + c • g' y) =ᶠ[𝓝 x] (fun y ↦ f y + c • g y) := by
    filter_upwards [hfeq, hgeq] with y hfy hgy
    rw [hfy, hgy]
  rw [← mooreLinearization_congr_germ A heq, mooreLinearization_add_smul A hf' hg',
    mooreLinearization_congr_germ A hfeq, mooreLinearization_congr_germ A hgeq]

/-- The linearized maximum principle needs only the local C² germ. -/
theorem mooreLinearization_nonpos_of_localMax_at {n : ℕ}
    {A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    {f : CoordinateSpace n 4 → ℝ} {x : CoordinateSpace n 4}
    (hA : (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef) (hf : ContDiffAt ℝ 2 f x)
    (hmax : IsLocalMax f x) : mooreLinearization A f x ≤ 0 := by
  obtain ⟨f', hf', hfeq⟩ := exists_contDiff_extension_near_point hf
  have hm : IsLocalMax f' x := by
    filter_upwards [hmax, hfeq] with y hy hfy
    rw [hfy, hfeq.self_of_nhds]
    exact hy
  obtain ⟨C, hAC, hCA⟩ := OAI.LinearAlgebra.Moore.exists_quaternion_inverse_of_complexify_posDef (A x) hA
  have hn := mooreLinearization_nonpos_of_localMax C hA hAC hCA
    (OAI.LinearAlgebra.Moore.mooreDet_pos_of_complexify_posDef (A x) hA).le hf' hm
  rwa [mooreLinearization_congr_germ A hfeq] at hn

theorem mooreLinearization_smul_at {n : ℕ}
    (A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    {f : CoordinateSpace n 4 → ℝ} {x : CoordinateSpace n 4}
    (hf : ContDiffAt ℝ 2 f x) (c : ℝ) :
    mooreLinearization A (fun y ↦ c • f y) x = c * mooreLinearization A f x := by
  obtain ⟨f', hf', hfeq⟩ := exists_contDiff_extension_near_point hf
  have heq : (fun y ↦ c • f' y) =ᶠ[𝓝 x] (fun y ↦ c • f y) := by
    filter_upwards [hfeq] with y hy
    rw [hy]
  rw [← mooreLinearization_congr_germ A heq, mooreLinearization_smul A hf',
    mooreLinearization_congr_germ A hfeq]

end OAI.Analysis.PDE.Dirichlet
