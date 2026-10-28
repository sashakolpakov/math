import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.ComposeTensor
import OAI.Analysis.Normed.Function.Holder.Boundary.LowerJetHolder
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.HolderPullback

noncomputable section
open Set Filter
open scoped Topology
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I]
local instance doubleHolder1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance doubleHolder1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance doubleHolder2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance doubleHolder2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance doubleHolder3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance doubleHolder3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance doubleHolder4Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance doubleHolder4Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- A norm bound on the actual Hessian of a twice-field derivative. -/
def HasDoubleFieldHolderBound (K : Set E) (α : ℝ) (u : E → ℝ)
    (T W : E → E) (M : ℝ) : Prop :=
  ∃ H : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] E →L[ℝ] ℝ) α,
    (∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x =
      fderiv ℝ (fderiv ℝ (fieldDerivative (fieldDerivative u T) W)) x) ∧ ‖H‖ ≤ M

omit [FiniteDimensional ℝ E] in
theorem hasDoubleFieldHolderBound_of_C2Holder
    {Ω K : Set E} {hΩK : Ω ⊆ K} {α M : ℝ} {u : E → ℝ} {T W : E → E}
    (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) (hUn : ‖U‖ ≤ M)
    (hU : ∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x =
      fderiv ℝ (fderiv ℝ (fieldDerivative (fieldDerivative u T) W)) x) :
    HasDoubleFieldHolderBound K α u T W M := by
  refine ⟨U.val.2.2,hU,?_⟩
  exact ((le_max_right _ _).trans (le_max_right _ _)).trans hUn

omit [FiniteDimensional ℝ E] in
theorem double_field_constant_germ {u : E → ℝ} {T W : E → E} {v w x : E}
    (hT : T =ᶠ[𝓝 x] fun _ => v) (hW : W =ᶠ[𝓝 x] fun _ => w) :
    fieldDerivative (fieldDerivative u T) W =ᶠ[𝓝 x]
      OAI.Analysis.PDE.Dirichlet.directionalDerivative (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v) w := by
  have he : fieldDerivative u T =ᶠ[𝓝 x] OAI.Analysis.PDE.Dirichlet.directionalDerivative u v := by
    filter_upwards [hT] with y hy
    change fderiv ℝ u y (T y) = fderiv ℝ u y v
    rw [hy]
  filter_upwards [he.eventuallyEq_nhds,hW] with y hy hw
  change fderiv ℝ (fieldDerivative u T) y (W y) =
    fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v) y w
  rw [hy.fderiv_eq,hw]

omit [FiniteDimensional ℝ E] in
/-- Hessian bounds for every twice-coordinate derivative reconstruct the
whole fourth derivative; no prior fourth-order Hölder bound is used. -/
theorem exists_fourth_holder_of_double_derivatives
    (b : OrthonormalBasis I ℝ E) {S : Set E} {α M : ℝ}
    (hα : 0 ≤ α) (hM : 0 ≤ M) (u : E → ℝ) (hu : ContDiff ℝ 4 u)
    (B : I × I → OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] ℝ) α)
    (hB : ∀ i j (x : S), OAI.Analysis.Normed.Function.Holder.HolderMap.value (B (i,j)) x =
      fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (b i)) (b j))) x)
    (hBn : ∀ p, ‖B p‖ ≤ M) :
    HasFourthHolderBound S α u ((Fintype.card I : ℝ)^4*M) := by
  have h₁ : ContDiff ℝ 3 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have h₂ : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ u)) := h₁.fderiv_right (by norm_num)
  have h₃ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) := h₂.fderiv_right (by norm_num)
  apply exists_quadrilinear_holder_of_coordinates b hα hM _
    ((h₃.continuous_fderiv one_ne_zero).comp continuous_subtype_val)
    (fun i j k l => holderEvaluate (holderEvaluate (B (i,j)) (b k)) (b l))
  · intro i j k l
    exact (holderEvaluate_norm_le _ (b.norm_eq_one l).le).trans
      ((holderEvaluate_norm_le _ (b.norm_eq_one k).le).trans (hBn (i,j)))
  · intro i j k l x
    rw [value_holderEvaluate,value_holderEvaluate,hB,Function.comp_apply,
      fourth_derivative_directional_third u hu,
      OAI.Analysis.PDE.Nonlinear.third_derivative_directional_hessian _
        (OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (by norm_num) _)]

omit [FiniteDimensional ℝ E] in
/-- On a neighborhood where the periodic fields are constant, their
twice-field Hessian estimates are exactly the coordinate estimates. -/
theorem fourth_holder_of_constant_field_germs
    (b : OrthonormalBasis I ℝ E) {K S : Set E} (hSK : S ⊆ K) {α M : ℝ}
    (hα : 0 ≤ α) (hM : 0 ≤ M) (u : E → ℝ) (hu : ContDiff ℝ 4 u)
    (T : I → E → E)
    (hT : ∀ i (x : S), T i =ᶠ[𝓝 (x : E)] fun _ => b i)
    (hB : ∀ i j, HasDoubleFieldHolderBound K α u (T i) (T j) M) :
    HasFourthHolderBound S α u ((Fintype.card I : ℝ)^4*M) := by
  classical
  have hh (p : I × I) := hB p.1 p.2
  choose B hBv hBn using hh
  let ι : S → K := fun x => ⟨x,hSK x.property⟩
  have hι : Isometry ι := by
    apply isometry_iff_dist_eq.mpr
    intro x y
    rfl
  let B' (p : I × I) := OAI.Analysis.PDE.Schauder.holderIsometricPullback hα ι hι (B p)
  apply exists_fourth_holder_of_double_derivatives b hα hM u hu B'
  · intro i j x
    change OAI.Analysis.Normed.Function.Holder.HolderMap.value (B (i,j)) (ι x) = _
    rw [hBv]
    exact (double_field_constant_germ (hT i x) (hT j x)).fderiv.fderiv_eq
  · intro p
    exact (OAI.Analysis.PDE.Schauder.norm_holderIsometricPullback_le hα ι hι (B p)).trans (hBn p)

end OAI.Analysis.PDE.Elliptic
