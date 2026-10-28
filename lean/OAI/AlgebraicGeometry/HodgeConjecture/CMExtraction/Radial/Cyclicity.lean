import OAI.RepresentationTheory.Hecke.RadialDilation.Mem

/-! # Cyclicity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity

noncomputable section

/-! The actual radial input is cyclic under the invertible, normalized
dilation. This is proved from its ball-indicator definition. -/

open scoped Classical
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm OAI.RepresentationTheory.Hecke.RadialDilation.Mem.Realization

variable (q : ℕ) [Fact q.Prime]

def ball (n : ℤ) : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q := ⟨RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q n, RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall_mem q n⟩

def normalization : ℂ := (Real.rpow (q : ℝ) (3 / 2 : ℝ) : ℂ)

theorem normalization_ne_zero : normalization q ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  exact (Real.rpow_pos_of_pos (by exact_mod_cast (Fact.out : q.Prime).pos) _).ne'

theorem dilation_ball (n : ℤ) :
    RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q (ball q n) = normalization q • ball q (n + 1) := by
  apply Subtype.ext
  exact congrArg (fun f : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q → ℂ => normalization q • f)
    (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.inverseSubstitution_ball q (q : ℚ_[q]) 1 (by simp [Padic.norm_p]) n)

theorem dilation_injective : Function.Injective (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q) := by
  intro b c he
  apply Subtype.ext
  funext x
  have hq : (q : ℚ_[q]) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hx := congrArg (fun b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q => b.val (fun i => (q : ℚ_[q]) * x i)) he
  simp only [RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation_apply, ← mul_assoc, inv_mul_cancel₀ hq, one_mul] at hx
  exact mul_left_cancel₀ (normalization_ne_zero q) hx

theorem dilation_surjective : Function.Surjective (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q) := by
  have h : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q ≤ LinearMap.range ((RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q).subtype.comp (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q)) := by
    apply Submodule.span_le.mpr
    rintro f ⟨n, rfl⟩
    refine ⟨(normalization q)⁻¹ • ball q (n - 1), ?_⟩
    change (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ((normalization q)⁻¹ • ball q (n - 1))).val = _
    rw [map_smul, dilation_ball, smul_smul, inv_mul_cancel₀ (normalization_ne_zero q), one_smul]
    rw [sub_add_cancel]
    rfl
  intro b
  obtain ⟨c, hc⟩ := h b.property
  exact ⟨c, Subtype.ext hc⟩

def dilationEquiv : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q ≃ₗ[ℂ] RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q :=
  LinearEquiv.ofBijective (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q) ⟨dilation_injective q, dilation_surjective q⟩

theorem dilationEquiv_apply (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) : dilationEquiv q b = RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q b := rfl

theorem dilationEquiv_ball (n : ℤ) :
    dilationEquiv q (ball q n) = normalization q • ball q (n + 1) := dilation_ball q n

theorem dilationEquiv_zpow_ball (n : ℤ) :
    (dilationEquiv q ^ n) (ball q 0) = normalization q ^ n • ball q n := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
      rw [show (n : ℤ) + 1 = 1 + (n : ℤ) by omega, zpow_one_add, LinearEquiv.mul_apply,
        ih, map_smul, dilationEquiv_ball, smul_smul]
      rw [show 1 + (n : ℤ) = (n : ℤ) + 1 by omega, zpow_add₀ (normalization_ne_zero q), zpow_one]
  | pred n ih =>
      apply (dilationEquiv q).injective
      have hstep : dilationEquiv q ((dilationEquiv q ^ (-(n : ℤ) - 1)) (ball q 0)) =
          (dilationEquiv q ^ (-(n : ℤ))) (ball q 0) := by
        rw [← LinearEquiv.mul_apply, ← zpow_one_add, show 1 + (-(n : ℤ) - 1) = -(n : ℤ) by omega]
      rw [hstep, ih, map_smul, dilationEquiv_ball, sub_add_cancel, smul_smul]
      rw [← zpow_add_one₀ (normalization_ne_zero q), sub_add_cancel]

theorem radial_cyclic :
    Submodule.span ℂ (Set.range (fun n : ℤ => (dilationEquiv q ^ n) (ball q 0))) = ⊤ := by
  let S := Submodule.span ℂ (Set.range (fun n : ℤ => (dilationEquiv q ^ n) (ball q 0)))
  have hb (n : ℤ) : ball q n ∈ S := by
    have hmem : (dilationEquiv q ^ n) (ball q 0) ∈ S := Submodule.subset_span ⟨n, rfl⟩
    rw [dilationEquiv_zpow_ball] at hmem
    have h := S.smul_mem ((normalization q ^ n)⁻¹) hmem
    simpa only [smul_smul, inv_mul_cancel₀ (zpow_ne_zero _ (normalization_ne_zero q)), one_smul] using h
  have hle : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q ≤ S.map (RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q).subtype := by
    apply Submodule.span_le.mpr
    rintro f ⟨n, rfl⟩
    exact ⟨ball q n, hb n, rfl⟩
  apply top_unique
  intro b _
  obtain ⟨c, hc, he⟩ := hle b.property
  exact (Subtype.ext he : c = b) ▸ hc

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity
