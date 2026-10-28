import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.FiniteTangents
import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.MoorePhysical

noncomputable section
open Set Filter Module Metric
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite tangent basis and its pairwise sums turn direction-dependent
neighborhoods into one neighborhood supporting all first and second tangent
derivatives. No uniform neighborhood is assumed for the original family. -/
theorem exists_common_tangent_neighborhood
    {ι : Type*} [Fintype ι] (ℓ : E →L[ℝ] ℝ) (b : Basis ι ℝ ℓ.ker)
    {S : Set E} {a : E} {f : E → ℝ} (hf : ∀ x ∈ S, ContDiffAt ℝ 2 f x)
    (hlocal : ∀ v, ℓ v = 0 → ∃ O : Set E, IsOpen O ∧ a ∈ O ∧
      ContDiffOn ℝ 2 (constantDirectional f v) (S ∩ O) ∧
      ContDiffOn ℝ 2 (fun x ↦ fderiv ℝ (fderiv ℝ f) x v v) (S ∩ O)) :
    ∃ O : Set E, IsOpen O ∧ a ∈ O ∧
      (∀ v, ℓ v = 0 → ContDiffOn ℝ 2 (constantDirectional f v) (S ∩ O)) ∧
      (∀ v, ℓ v = 0 → ∀ w, ℓ w = 0 →
        ContDiffOn ℝ 2 (constantDirectional (constantDirectional f v) w) (S ∩ O)) := by
  classical
  obtain ⟨O₁,hO₁,ha₁,h₁⟩ := exists_common_contDiffOn_neighborhood
    (S := S) (x := a) (fun i : ι ↦ constantDirectional f (b i)) (by
      intro i
      obtain ⟨O,hO,ha,hfirst,hsecond⟩ := hlocal (b i) (b i).property
      exact ⟨O,hO,ha,hfirst⟩)
  obtain ⟨O₂,hO₂,ha₂,h₂⟩ := exists_common_contDiffOn_neighborhood
    (S := S) (x := a) (fun i : ι ↦ fun x ↦ fderiv ℝ (fderiv ℝ f) x (b i) (b i)) (by
      intro i
      obtain ⟨O,hO,ha,hfirst,hsecond⟩ := hlocal (b i) (b i).property
      exact ⟨O,hO,ha,hsecond⟩)
  obtain ⟨O₃,hO₃,ha₃,h₃⟩ := exists_common_contDiffOn_neighborhood
    (S := S) (x := a) (fun ij : ι × ι ↦ fun x ↦
      fderiv ℝ (fderiv ℝ f) x ((b ij.1 : E) + b ij.2) ((b ij.1 : E) + b ij.2)) (by
      intro ij
      have hz : ℓ ((b ij.1 : E) + b ij.2) = 0 := by
        have hleft : ℓ (b ij.1) = 0 := (b ij.1).property
        have hright : ℓ (b ij.2) = 0 := (b ij.2).property
        rw [map_add,hleft,hright,add_zero]
      obtain ⟨O,hO,ha,hfirst,hsecond⟩ := hlocal _ hz
      exact ⟨O,hO,ha,hsecond⟩)
  refine ⟨O₁ ∩ O₂ ∩ O₃,(hO₁.inter hO₂).inter hO₃,⟨⟨ha₁,ha₂⟩,ha₃⟩,?_,?_⟩
  · apply contDiffOn_tangents_of_basis ℓ b f
    intro i
    exact (h₁ i).mono (fun x hx ↦ ⟨hx.1,hx.2.1.1⟩)
  · apply contDiffOn_second_tangents_of_diagonal_basis ℓ b
      (fun x hx ↦ hf x hx.1)
    · intro i
      exact (h₂ i).mono (fun x hx ↦ ⟨hx.1,hx.2.1.2⟩)
    · intro i j
      exact (h₃ (i,j)).mono (fun x hx ↦ ⟨hx.1,hx.2.2⟩)

/-- Direction-dependent neighborhoods can also be made into a single genuine
half-ball. Its radius is allowed to shrink, as required by local regularity. -/
theorem exists_common_tangent_halfball
    {ι : Type*} [Fintype ι] (ℓ : E →L[ℝ] ℝ) (b : Basis ι ℝ ℓ.ker)
    {R : ℝ} (hR : 0 < R) {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hlocal : ∀ v, ℓ v = 0 → ∃ O : Set E, IsOpen O ∧ (0 : E) ∈ O ∧
      ContDiffOn ℝ 2 (constantDirectional f v) (({x | 0 ≤ ℓ x} ∩ ball 0 R) ∩ O) ∧
      ContDiffOn ℝ 2 (fun x ↦ fderiv ℝ (fderiv ℝ f) x v v)
        (({x | 0 ≤ ℓ x} ∩ ball 0 R) ∩ O)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧
      (∀ v, ℓ v = 0 → ContDiffOn ℝ 2 (constantDirectional f v)
        ({x | 0 ≤ ℓ x} ∩ ball 0 ρ)) ∧
      (∀ v, ℓ v = 0 → ∀ w, ℓ w = 0 →
        ContDiffOn ℝ 2 (constantDirectional (constantDirectional f v) w)
          ({x | 0 ≤ ℓ x} ∩ ball 0 ρ)) := by
  obtain ⟨O,hO,hzero,hfirst,hsecond⟩ := exists_common_tangent_neighborhood
    ℓ b (fun _ _ ↦ hf.contDiffAt) hlocal
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hO 0 hzero
  let ρ := min R ε
  have hρ : 0 < ρ := lt_min hR hε
  have hsub : ({x | 0 ≤ ℓ x} ∩ ball 0 ρ) ⊆ ({x | 0 ≤ ℓ x} ∩ ball 0 R) ∩ O := by
    intro x hx
    exact ⟨⟨hx.1,lt_of_lt_of_le hx.2 (min_le_left R ε)⟩,
      hball (lt_of_lt_of_le hx.2 (min_le_right R ε))⟩
  exact ⟨ρ,hρ,min_le_left _ _,fun v hv ↦ (hfirst v hv).mono hsub,
    fun v hv w hw ↦ (hsecond v hv w hw).mono hsub⟩

section Physical
open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
variable {m n : ℕ}
local notation "X" => EuclideanSpace ℝ (Fin m)
local notation "Y" => CoordinateSpace n 4

/-- The local version needed by the deformation argument. Each tangent
direction may have its own neighborhood; a finite basis and polarization
produce one smaller half-ball with an actual C⁴ representative. -/
theorem exists_C4_moore_chart_of_local_tangents
    {ψ : Y → ℝ} (hψ : ContDiff ℝ 2 ψ) (G : X → Y) (P : Y → X)
    (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P)
    (load : Y → ℝ) (hl : ContDiff ℝ ∞ load)
    (ℓ : X →L[ℝ] ℝ) (ν : X) (hν : ℓ ν = 1) {R : ℝ} (hR : 0 < R)
    (hPG : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R), (fun y ↦ P (G y)) =ᶠ[𝓝 x] id)
    (hGP : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R), (fun y ↦ G (P y)) =ᶠ[𝓝 (G x)] id)
    (hlocal : ∀ v, ℓ v = 0 → ∃ O : Set X, IsOpen O ∧ (0 : X) ∈ O ∧
      ContDiffOn ℝ 2 (constantDirectional (ψ ∘ G) v)
        (({x | 0 ≤ ℓ x} ∩ ball 0 R) ∩ O) ∧
      ContDiffOn ℝ 2 (fun x ↦ fderiv ℝ (fderiv ℝ (ψ ∘ G)) x v v)
        (({x | 0 ≤ ℓ x} ∩ ball 0 R) ∩ O))
    (hpos : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R),
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x))).PosDef)
    (he : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R),
      OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x)) = load (G x)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧ ∃ g : X → ℝ, ContDiff ℝ 4 g ∧
      EqOn g (ψ ∘ G) ({x | 0 ≤ ℓ x} ∩ closedBall 0 ρ) := by
  obtain ⟨ρ,hρ,hρR,hfirst,hsecond⟩ := exists_common_tangent_halfball ℓ
    (Module.finBasis ℝ ℓ.ker) hR (hψ.comp (hG.of_le (by simp))) hlocal
  have hsub : ({x | 0 ≤ ℓ x} ∩ ball 0 ρ) ⊆ {x | 0 ≤ ℓ x} ∩ ball 0 R := by
    intro x hx
    exact ⟨hx.1,lt_of_lt_of_le hx.2 hρR⟩
  obtain ⟨g,hg,heq⟩ := exists_C4_moore_chart_representative hψ G P hG hP load hl
    ℓ ν hν hρ (fun x hx ↦ hPG x (hsub hx)) (fun x hx ↦ hGP x (hsub hx))
    hfirst hsecond (fun x hx ↦ hpos x (hsub hx)) (fun x hx ↦ he x (hsub hx))
  exact ⟨ρ/4,by positivity,(by linarith),g,hg,heq⟩

end Physical
end OAI.Analysis.PDE.Dirichlet
