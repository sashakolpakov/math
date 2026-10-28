import OAI.Analysis.PDE.Dirichlet.AffineFamily

open Set Filter
open scoped Topology Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

/-- The forcing constant is uniform also in a compact family of rigid fields,
not just in the unknown solution. -/
theorem exists_compact_family_rigid_forcing {P : Type*} [TopologicalSpace P] [CompactSpace P]
    {n : ℕ} {B₀ F : CoordinateSpace n 4 → ℝ}
    (hB₀ : ContDiff ℝ 3 B₀) (hF : ContDiff ℝ 1 F)
    {e : P → CoordinateSpace n 4} {R : P → Matrix (Fin n) (Fin n) Q}
    (he : Continuous e) (hR : Continuous R) (hskew : ∀ p, (R p)ᴴ = -R p)
    {S : Set (CoordinateSpace n 4)} (hS : IsCompact S) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p u, ContDiff ℝ 3 u → ∀ x ∈ S,
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z ↦ B₀ z + u z) x)).PosDef →
      κ ≤ OAI.LinearAlgebra.Moore.mooreDifferential n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z ↦ B₀ z + u z) x) 1 →
      (fun y ↦ OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z ↦ B₀ z + u z) y)) =ᶠ[𝓝 x] F →
      |mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z ↦ B₀ z + u z))
        (affineDerivative u (e p) (realMatrixAction (realRepresentation (R p)))) x| ≤
        C * OAI.LinearAlgebra.Moore.mooreDifferential n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z ↦ B₀ z + u z) x) 1 := by
  let A : P → CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 :=
    fun p ↦ realMatrixAction (realRepresentation (R p))
  have hA : Continuous A := continuous_realMatrixAction.comp (continuous_realRepresentation hR)
  let T : Set (CoordinateSpace n 4 × P) := S ×ˢ univ
  have hT : IsCompact T := hS.prod isCompact_univ
  have hD : Continuous (fun z : CoordinateSpace n 4 × P ↦
      ‖OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (affineDerivative B₀ (e z.2) (A z.2)) z.1)‖) :=
    (continuous_complexify_map (continuous_quaternionHessian_affineDerivative_family hB₀
      (he.comp continuous_snd) (hA.comp continuous_snd) continuous_fst)).norm
  obtain ⟨K₀, hK₀⟩ := hT.bddAbove_image hD.continuousOn
  let K := max K₀ 0 + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hDle : ∀ p x, x ∈ S →
      ‖OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (affineDerivative B₀ (e p) (A p)) x)‖ ≤ K := by
    intro p x hx
    have h := hK₀ (mem_image_of_mem _ (show (x, p) ∈ T from ⟨hx, mem_univ _⟩))
    exact h.trans (by dsimp [K]; linarith [le_max_left K₀ 0])
  have hXF : Continuous (fun z : CoordinateSpace n 4 × P ↦
      |affineDerivative F (e z.2) (A z.2) z.1|) :=
    (continuous_affineDerivative_family hF (he.comp continuous_snd)
      (hA.comp continuous_snd) continuous_fst).abs
  obtain ⟨L₀, hL₀⟩ := hT.bddAbove_image hXF.continuousOn
  let L := max L₀ 0 + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hFle : ∀ p x, x ∈ S → |affineDerivative F (e p) (A p) x| ≤ L := by
    intro p x hx
    have h := hL₀ (mem_image_of_mem _ (show (x, p) ∈ T from ⟨hx, mem_univ _⟩))
    exact h.trans (by dsimp [L]; linarith [le_max_left L₀ 0])
  refine ⟨L / κ + K, by positivity, ?_⟩
  intro p u hu x hx hpos htrace heq
  have hXB : ContDiff ℝ 2 (affineDerivative B₀ (e p) (A p)) :=
    contDiff_affineDerivative hB₀ (by norm_num) _ _
  obtain ⟨hp, hm⟩ := complexify_shift_posSemidef _
    (quaternionHessian_isHermitian OAI.Analysis.Calculus.Quaternion.fourSlots hXB.contDiffAt) (hDle p x hx)
  exact mooreLinearization_rigid_forcing hB₀ hu (e p) (R p) (hskew p)
    (hF.differentiable (by norm_num) x) heq hκ hL.le hpos htrace (hFle p x hx) hp
    (by simpa only [neg_one_smul] using hm)

end OAI.Analysis.PDE.Dirichlet
