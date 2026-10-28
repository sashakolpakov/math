import OAI.Geometry.ComplexBall.PrescribedSignsPeriodTransport

/-! # Dual Transport -/

namespace OAI.Geometry.ComplexBall.DualTransport.PrescribedSigns.Intrinsic

noncomputable section

open scoped Classical

lemma active_form_nondegenerate (B : PrescribedSignsB.Bilin) (hB : PrescribedSignsB.HermitianB B)
    (hp : ∀ x : PrescribedSignsB.Vec, x ≠ 0 → x 2 = 0 → 0 < (B x (star x)).re)
    (hn : (B (PrescribedSignsB.lineVector 0) (star (PrescribedSignsB.lineVector 0))).re < 0) :
    Function.Injective B.flip := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro y hy
  change y = 0
  by_contra hne
  have hz (x : PrescribedSignsB.Vec) : B x y = 0 := congrArg (fun f : Module.Dual ℂ PrescribedSignsB.Vec => f x) hy
  have hs : star y ≠ 0 := by simpa only [star_ne_zero] using hne
  have ho : B (PrescribedSignsB.lineVector 0) (star (star y)) = 0 := by simpa only [star_star] using hz (PrescribedSignsB.lineVector 0)
  have hpos := PrescribedSignsB.orthogonal_positive B hB hp 0 hn (star y) hs ho
  rw [star_star, hz, Complex.zero_re] at hpos
  exact (lt_irrefl 0) hpos

def conjugatePlaceDual (B : PrescribedSignsB.Bilin) (hB : Function.Injective B.flip) :
    PrescribedSignsB.Vec ≃ₗ[ℂ] Module.Dual ℂ PrescribedSignsB.Vec :=
  B.flip.linearEquivOfInjective hB (by simp)

lemma conjugatePlaceDual_annihilator (B : PrescribedSignsB.Bilin) (hB : Function.Injective B.flip)
    (z : PrescribedSignsB.BallChart) :
    (Submodule.span ℂ {PrescribedSignsB.lineVector z}).dualAnnihilator.comap
      (conjugatePlaceDual B hB).toLinearMap = (B (PrescribedSignsB.lineVector z)).ker := by
  ext y
  rw [Submodule.mem_comap, Submodule.mem_dualAnnihilator, LinearMap.mem_ker]
  change (∀ x ∈ Submodule.span ℂ {PrescribedSignsB.lineVector z}, B x y = 0) ↔ B (PrescribedSignsB.lineVector z) y = 0
  constructor
  · intro h
    exact h _ (Submodule.subset_span (Set.mem_singleton _))
  · intro h x hx
    have hle : Submodule.span ℂ {PrescribedSignsB.lineVector z} ≤ (B.flip y).ker := by
      apply Submodule.span_le.mpr
      intro v hv
      obtain rfl := Set.mem_singleton_iff.mp hv
      exact h
    exact hle hx

/-- The prescribed conjugate-place kernel is the actual dual of the
quotient by the moving line, via the Hermitian form. -/
def activeQuotientDual (B : PrescribedSignsB.Bilin) (hB : Function.Injective B.flip) (z : PrescribedSignsB.BallChart) :
    (B (PrescribedSignsB.lineVector z)).ker ≃ₗ[ℂ] Module.Dual ℂ (PrescribedSignsB.Vec ⧸ Submodule.span ℂ {PrescribedSignsB.lineVector z}) :=
  (LinearEquiv.ofEq _ _ (conjugatePlaceDual_annihilator B hB z).symm) ≪≫ₗ
    (conjugatePlaceDual B hB).ofSubmodule' (Submodule.span ℂ {PrescribedSignsB.lineVector z}).dualAnnihilator ≪≫ₗ
    (Submodule.dualQuotEquivDualAnnihilator (Submodule.span ℂ {PrescribedSignsB.lineVector z})).symm

lemma scaled_form_nondegenerate (B : PrescribedSignsB.Bilin) (hB : Function.Injective B.flip)
    (a : ℂ) (ha : a ≠ 0) : Function.Injective (a • B).flip := by
  intro x y he
  apply hB
  have hh := congrArg (fun f : Module.Dual ℂ PrescribedSignsB.Vec => a⁻¹ • f) he
  apply LinearMap.ext
  intro v
  have hv := congrArg (fun f : Module.Dual ℂ PrescribedSignsB.Vec => f v) hh
  simpa only [LinearMap.smul_apply, LinearMap.flip_apply, smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ ha, one_mul] using hv

lemma scaled_kernel (B : PrescribedSignsB.Bilin) (a : ℂ) (ha : a ≠ 0) (z : PrescribedSignsB.BallChart) :
    ((a • B) (PrescribedSignsB.lineVector z)).ker = (B (PrescribedSignsB.lineVector z)).ker := by
  ext y
  simp only [LinearMap.mem_ker, LinearMap.smul_apply, smul_eq_mul, mul_eq_zero,
    ha, false_or]

/-- Including the one-dimensional multiplicity form scales the dual
identification by its nonzero coefficient and leaves the prescribed kernel unchanged. -/
def activeLineQuotientDual (B : PrescribedSignsB.Bilin) (hB : Function.Injective B.flip)
    (a : ℂ) (ha : a ≠ 0) (z : PrescribedSignsB.BallChart) :
    (B (PrescribedSignsB.lineVector z)).ker ≃ₗ[ℂ] Module.Dual ℂ (PrescribedSignsB.Vec ⧸ Submodule.span ℂ {PrescribedSignsB.lineVector z}) :=
  LinearEquiv.ofEq _ _ (scaled_kernel B a ha z).symm ≪≫ₗ
    activeQuotientDual (a • B) (scaled_form_nondegenerate B hB a ha) z

lemma activeLineQuotientDual_apply (B : PrescribedSignsB.Bilin) (hB : Function.Injective B.flip)
    (a : ℂ) (ha : a ≠ 0) (z : PrescribedSignsB.BallChart) (y : (B (PrescribedSignsB.lineVector z)).ker) (x : PrescribedSignsB.Vec) :
    activeLineQuotientDual B hB a ha z y (Submodule.Quotient.mk x) = a * B x y := by
  rfl

/-- The two multiplicity lines give the two quotient-dual factors of the
orthogonal sum, each using its own Hermitian coefficient. -/
def activeSumQuotientDual (B : PrescribedSignsB.Bilin) (hB : Function.Injective B.flip)
    (a : Fin 2 → ℂ) (ha : ∀ i, a i ≠ 0) (z : PrescribedSignsB.BallChart) :
    ((B (PrescribedSignsB.lineVector z)).ker × (B (PrescribedSignsB.lineVector z)).ker) ≃ₗ[ℂ]
      Module.Dual ℂ (PrescribedSignsB.Vec ⧸ Submodule.span ℂ {PrescribedSignsB.lineVector z}) ×
      Module.Dual ℂ (PrescribedSignsB.Vec ⧸ Submodule.span ℂ {PrescribedSignsB.lineVector z}) :=
  (activeLineQuotientDual B hB (a 0) (ha 0) z).prodCongr
    (activeLineQuotientDual B hB (a 1) (ha 1) z)

end

end OAI.Geometry.ComplexBall.DualTransport.PrescribedSigns.Intrinsic
