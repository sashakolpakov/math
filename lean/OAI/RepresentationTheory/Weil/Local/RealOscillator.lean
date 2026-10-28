import OAI.RepresentationTheory.Weil.Local.RealLevi
import OAI.RepresentationTheory.Weil.Local.UnitaryInner

/-! # Real Oscillator -/

namespace OAI.RepresentationTheory.Weil.Local.RealOscillator.Construction

noncomputable section

section

/-! The actual real oscillator action extends uniquely to the full L² space. -/

open _root_.MeasureTheory

theorem real_testToL2_dense (n : ℕ) : DenseRange (UnitaryInner.Construction.testToL2 ℝ n) := by
  have hd := SchwartzMap.denseRange_toLpCLM (E := FunctionsMetaplectic.Construction.Position ℝ n) (F := ℂ)
    (μ := UnitaryInner.Construction.referencePositionMeasure ℝ n) (p := 2) (by norm_num)
  intro x
  apply closure_mono _ (hd x)
  rintro _ ⟨f, rfl⟩
  exact ⟨RealTestSpace.Construction.realSchwartzEquiv n f, rfl⟩

def realL2Oscillator (n : ℕ) (ψ : AddChar ℝ ℂ) (a : FunctionsMetaplectic.Construction.Oscillator ℝ n ψ) :
    Lp ℂ 2 (UnitaryInner.Construction.referencePositionMeasure ℝ n) ≃ₗᵢ[ℂ] Lp ℂ 2 (UnitaryInner.Construction.referencePositionMeasure ℝ n) :=
  a.val.2.extendOfIsometry (UnitaryInner.Construction.testToL2 ℝ n) (UnitaryInner.Construction.testToL2 ℝ n)
    (real_testToL2_dense n) (real_testToL2_dense n)
    (fun f => by rw [UnitaryInner.Construction.testToL2_norm, UnitaryInner.Construction.testToL2_norm, a.property.1])

theorem realL2Oscillator_apply (n : ℕ) (ψ : AddChar ℝ ℂ) (a : FunctionsMetaplectic.Construction.Oscillator ℝ n ψ)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) :
    Construction.realL2Oscillator n ψ a (UnitaryInner.Construction.testToL2 ℝ n f) = UnitaryInner.Construction.testToL2 ℝ n (a.val.2 f) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ f

theorem realL2Oscillator_one (n : ℕ) (ψ : AddChar ℝ ℂ) : Construction.realL2Oscillator n ψ 1 = 1 := by
  apply DFunLike.ext'
  apply (real_testToL2_dense n).equalizer (Construction.realL2Oscillator n ψ 1).continuous (continuous_id)
  funext f
  exact realL2Oscillator_apply n ψ 1 f

theorem realL2Oscillator_mul (n : ℕ) (ψ : AddChar ℝ ℂ) (a b : FunctionsMetaplectic.Construction.Oscillator ℝ n ψ) :
    Construction.realL2Oscillator n ψ (a * b) = Construction.realL2Oscillator n ψ a * Construction.realL2Oscillator n ψ b := by
  apply DFunLike.ext'
  apply (real_testToL2_dense n).equalizer (Construction.realL2Oscillator n ψ (a * b)).continuous
    ((Construction.realL2Oscillator n ψ a).continuous.comp (Construction.realL2Oscillator n ψ b).continuous)
  funext f
  change Construction.realL2Oscillator n ψ (a * b) (UnitaryInner.Construction.testToL2 ℝ n f) =
    Construction.realL2Oscillator n ψ a (Construction.realL2Oscillator n ψ b (UnitaryInner.Construction.testToL2 ℝ n f))
  rw [realL2Oscillator_apply, realL2Oscillator_apply, realL2Oscillator_apply]
  rfl

def realL2OscillatorHom (n : ℕ) (ψ : AddChar ℝ ℂ) :
    FunctionsMetaplectic.Construction.Oscillator ℝ n ψ →* (Lp ℂ 2 (UnitaryInner.Construction.referencePositionMeasure ℝ n) ≃ₗᵢ[ℂ] Lp ℂ 2 (UnitaryInner.Construction.referencePositionMeasure ℝ n)) where
  toFun := Construction.realL2Oscillator n ψ
  map_one' := realL2Oscillator_one n ψ
  map_mul' := realL2Oscillator_mul n ψ

theorem realL2Oscillator_scalar (n : ℕ) (ψ : AddChar ℝ ℂ) (a : FunctionsMetaplectic.Construction.Oscillator ℝ n ψ) (z : ℂ)
    (h : ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n, a.val.2 f = z • f)
    (f : Lp ℂ 2 (UnitaryInner.Construction.referencePositionMeasure ℝ n)) : Construction.realL2Oscillator n ψ a f = z • f := by
  have he := (real_testToL2_dense n).equalizer (Construction.realL2Oscillator n ψ a).continuous
    (by fun_prop : Continuous (fun g : Lp ℂ 2 (UnitaryInner.Construction.referencePositionMeasure ℝ n) => z • g))
    (show Construction.realL2Oscillator n ψ a ∘ UnitaryInner.Construction.testToL2 ℝ n =
      (fun g => z • g) ∘ UnitaryInner.Construction.testToL2 ℝ n from by
        funext g
        change Construction.realL2Oscillator n ψ a (UnitaryInner.Construction.testToL2 ℝ n g) = z • UnitaryInner.Construction.testToL2 ℝ n g
        rw [realL2Oscillator_apply, h, map_smul])
  exact congrFun he f

end

/-! Identifying the actual L² oscillator action by test-function pairings. -/

open _root_.MeasureTheory
open scoped InnerProductSpace

theorem L2_toLp_inner {E : Type} [MeasurableSpace E] (μ : Measure E)
    {f g : E → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hf.toLp f, hg.toLp g⟫_ℂ = ∫ x, ⟪f x, g x⟫_ℂ ∂μ := by
  change (∫ x, ⟪(hf.toLp f) x, (hg.toLp g) x⟫_ℂ ∂μ) = _
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]

theorem realL2Oscillator_eq_of_pairings {n : ℕ} (ψ : AddChar ℝ ℂ)
    (a : FunctionsMetaplectic.Construction.Oscillator ℝ n ψ) (f g : Lp ℂ 2 (UnitaryInner.Construction.referencePositionMeasure ℝ n))
    (h : ∀ φ : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n,
      ⟪f, UnitaryInner.Construction.testToL2 ℝ n φ⟫_ℂ = ⟪g, UnitaryInner.Construction.testToL2 ℝ n (a.val.2 φ)⟫_ℂ) :
    Construction.realL2Oscillator n ψ a f = g := by
  apply ext_inner_right ℂ
  have he := (real_testToL2_dense n).equalizer
    (by fun_prop : Continuous (fun v => ⟪realL2Oscillator n ψ a f, v⟫_ℂ))
    (by fun_prop : Continuous (fun v => ⟪g, v⟫_ℂ))
    (show (fun v => ⟪Construction.realL2Oscillator n ψ a f, v⟫_ℂ) ∘ UnitaryInner.Construction.testToL2 ℝ n =
      (fun v => ⟪g, v⟫_ℂ) ∘ UnitaryInner.Construction.testToL2 ℝ n from by
        funext θ
        let φ := a.val.2.symm θ
        have hθ : a.val.2 φ = θ := a.val.2.apply_symm_apply θ
        change ⟪Construction.realL2Oscillator n ψ a f, UnitaryInner.Construction.testToL2 ℝ n θ⟫_ℂ = ⟪g, UnitaryInner.Construction.testToL2 ℝ n θ⟫_ℂ
        rw [← hθ, ← realL2Oscillator_apply, LinearIsometryEquiv.inner_map_map]
        rw [realL2Oscillator_apply]
        exact h φ)
  exact congrFun he

theorem realL2Oscillator_toLp_eq_of_integrals {n : ℕ} (ψ : AddChar ℝ ℂ)
    (a : FunctionsMetaplectic.Construction.Oscillator ℝ n ψ) {f g : FunctionsMetaplectic.Construction.Position ℝ n → ℂ}
    (hf : MemLp f 2 (UnitaryInner.Construction.referencePositionMeasure ℝ n))
    (hg : MemLp g 2 (UnitaryInner.Construction.referencePositionMeasure ℝ n))
    (h : ∀ φ : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n,
      (∫ x, ⟪f x, φ.val x⟫_ℂ ∂ UnitaryInner.Construction.referencePositionMeasure ℝ n) =
        ∫ x, ⟪g x, (a.val.2 φ).val x⟫_ℂ ∂ UnitaryInner.Construction.referencePositionMeasure ℝ n) :
    Construction.realL2Oscillator n ψ a (hf.toLp f) = hg.toLp g := by
  apply realL2Oscillator_eq_of_pairings
  intro φ
  exact (L2_toLp_inner _ hf (UnitaryInner.Construction.test_memLp_two ℝ n φ)).trans
    ((h φ).trans (L2_toLp_inner _ hg (UnitaryInner.Construction.test_memLp_two ℝ n (a.val.2 φ))).symm)

end

end OAI.RepresentationTheory.Weil.Local.RealOscillator.Construction
