import OAI.Analysis.Normed.Function.Sobolev.Reflection.Family
import OAI.Analysis.Normed.Function.Sobolev.PiEmbedding

open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.Normed.Function.Sobolev

open OAI.Analysis.PDE.Weak

/-- Finite-order Sobolev embedding up to the flat boundary. The extension
is an actual finite linear combination of normal reflections, with
Lagrange coefficients matching all the required normal derivatives. -/
theorem exists_contDiff_halfspace_representative_of_compact_derivative_family
    {d N q : ℕ} (k : Fin d) (hN : d + q < N)
    (U : List (Fin d) → (Fin d → ℝ) → ℝ)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K)
    (hUK : ∀α, α.length ≤ N → ∀ᵐx, x ∉ K → U α x = 0)
    (hU2 : ∀α, α.length ≤ N → MemLp (U α) 2)
    (hUD : ∀α, α.length < N → ∀i : Fin d,
      OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivativeOn volume {x | 0 < x k}
        (Pi.single i 1) (U α) (U (i :: α))) :
    ∃g : (Fin d → ℝ) → ℝ, ContDiff ℝ q g ∧
      ∀ᵐx, 0 < x k → U [] x = g x := by
  have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le k.val) k.isLt
  have hUi (α : List (Fin d)) (hα : α.length ≤ N) : Integrable (U α) :=
    integrable_of_memLp_two_compact_support_pi (hU2 α hα) hK (hUK α hα)
  obtain ⟨g,hg,hgeq⟩ := exists_contDiff_pi_representative_of_compact_derivative_family
    hd hN (reflectedDerivativeFamily N k U)
    (isCompact_reflectedSupport k reflectionNode hK)
    (fun α hα ↦ reflectedDerivativeFamily_zero_off N k U α (hUK α hα))
    (fun α hα ↦ reflectedDerivativeFamily_memLp N k U α (hU2 α hα))
    (fun α hα i ↦ reflectedDerivativeFamily_weakDerivative N k i U α hα
      (hUi α hα.le) (hUi (i :: α) (by simpa using hα)) (hUD α hα i))
  refine ⟨g,hg,?_⟩
  filter_upwards [hgeq] with x hx
  intro hxk
  rw [reflectedDerivativeFamily_eq N k U [] hxk] at hx
  exact hx

theorem exists_contDiff_halfspace_representative_of_compact_L2_derivatives
    {d N q : ℕ} (k : Fin d) (hN : d + q < N)
    (U : List (Fin d) → Lp ℝ 2 (volume : Measure (Fin d → ℝ)))
    {K : Set (Fin d → ℝ)} (hK : IsCompact K)
    (hUK : ∀α, α.length ≤ N → ∀ᵐx, x ∉ K → U α x = 0)
    (hUD : ∀α, α.length < N → ∀i : Fin d,
      OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivativeOn volume {x | 0 < x k}
        (Pi.single i 1) (U α) (U (i :: α))) :
    ∃g : (Fin d → ℝ) → ℝ, ContDiff ℝ q g ∧
      ∀ᵐx, 0 < x k → U [] x = g x :=
  exists_contDiff_halfspace_representative_of_compact_derivative_family k hN
    (fun α ↦ U α) hK hUK (fun α _ ↦ Lp.memLp (U α)) hUD

end OAI.Analysis.Normed.Function.Sobolev
