import OAI.RepresentationTheory.Weil.Local.FiniteQuadraticPhase
import OAI.RepresentationTheory.Weil.Local.GaussianCompact

/-! # Compact Quadratic Phase -/

namespace OAI.RepresentationTheory.Weil.Local

noncomputable section

/-! Passing the finite quadratic phase theorem to compact open local integrals. -/

open _root_.MeasureTheory
open scoped Classical

section

theorem FiniteQuadratic.Construction.QuadraticCharacter.compact_integral_phase_eighth
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (q : FiniteQuadratic.Construction.QuadraticCharacter E) (hc : Continuous (fun x => q x))
    (U V : OpenAddSubgroup E) (hU : IsCompact (U : Set E))
    (hiso : ∀ x ∈ V, q x = 1)
    (hpair : ∀ x ∈ V, ∀ y ∈ U, q.polar x y = 1)
    (hG : (∫ x in (U : Set E), q x ∂μ) ≠ 0) :
    FunctionsMetaplectic.Construction.phase (∫ x in (U : Set E), q x ∂μ) ^ 8 = 1 := by
  let H := V.toAddSubgroup.addSubgroupOf U.toAddSubgroup
  let : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have hHopen : IsOpen (H : Set U) := U.toAddSubgroup.addSubgroupOf_isOpen V.toAddSubgroup V.isOpen
  let : Finite (U ⧸ H) := H.quotient_finite_of_isOpen hHopen
  let : Fintype (U ⧸ H) := Fintype.ofFinite _
  let p := q.restrict U.toAddSubgroup
  have hHi : p.Isotropic H := fun x hx => hiso x.val hx
  have hHr : H ≤ p.orthogonal ⊤ := fun x hx y _ => hpair x.val hx y.val y.property
  let d := p.descend H hHi hHr
  let G := ∫ x in (U : Set E), q x ∂μ
  have hsum (x : U) : (∑ z : U ⧸ H, q (x.val + z.out.val)) = d.gauss := by
    have hv (z : U ⧸ H) : q (x.val + z.out.val) = d (QuotientAddGroup.mk x + z) := by
      change p (x + z.out) = _
      rw [← p.descend_mk H hHi hHr, QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
    simp only [hv]
    exact Equiv.sum_comp (Equiv.addLeft (QuotientAddGroup.mk x)) d
  have htranslate (t : U) : (∫ x in (U : Set E), q (x + t.val) ∂μ) = G := by
    let f := (U : Set E).indicator (fun x => q x)
    have hf : (U : Set E).indicator (fun x => q (x + t.val)) = fun x => f (x + t.val) := by
      funext x
      have hmem : x + t.val ∈ U ↔ x ∈ U := U.add_mem_cancel_right t.property
      by_cases hx : x ∈ U
      · simp [f, hx, hmem.mpr hx]
      · have hxt : x + t.val ∉ U := fun h => hx (hmem.mp h)
        simp [f, hx, hxt]
    rw [← integral_indicator U.isOpen.measurableSet, hf, integral_add_right_eq_self]
    exact integral_indicator U.isOpen.measurableSet
  have hscale : (Fintype.card (U ⧸ H) : ℂ) * G = (μ.real (U : Set E) : ℂ) * d.gauss := by
    calc
      _ = ∑ z : U ⧸ H, ∫ x in (U : Set E), q (x + z.out.val) ∂μ := by
        simp only [htranslate, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∫ x in (U : Set E), ∑ z : U ⧸ H, q (x + z.out.val) ∂μ := by
        rw [integral_finsetSum]
        intro z _
        exact (hc.comp (continuous_id.add continuous_const)).continuousOn.integrableOn_compact hU
      _ = ∫ _ in (U : Set E), d.gauss ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with x hx
        exact hsum ⟨x, hx⟩
      _ = _ := by simp only [integral_const, Complex.real_smul, Measure.real,
        Measure.restrict_apply_univ]
  have hd : d.gauss ≠ 0 := by
    intro hd
    rw [hd, mul_zero] at hscale
    exact (mul_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hG) hscale
  have hphase : FunctionsMetaplectic.Construction.phase G = FunctionsMetaplectic.Construction.phase d.gauss := by
    have h := congrArg FunctionsMetaplectic.Construction.phase hscale
    rw [← Complex.ofReal_natCast] at h
    rw [Gaussian.Construction.phase_positive_mul (Fintype.card (U ⧸ H) : ℝ) (Nat.cast_pos.mpr Fintype.card_pos),
      Gaussian.Construction.phase_positive_mul (μ.real (U : Set E)) (NonarchimedeanFourier.Construction.compact_open_subgroup_real_pos μ U hU)] at h
    exact h
  rw [show (∫ x in (U : Set E), q x ∂μ) = G from rfl, hphase]
  exact d.phase_gauss_eighth hd

end

def CompactQuadraticPhase.Construction.localQuadraticCharacter {k : Type*} [Field k] [CharZero k]
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1) (a : k) : FiniteQuadratic.Construction.QuadraticCharacter k where
  toFun x := ψ (a * x ^ 2 / 2)
  polar :=
    { toFun x :=
        { toFun y := ψ (a * x * y)
          map_zero_eq_one' := by simp
          map_add_eq_mul' y z := by rw [mul_add, ψ.map_add_eq_mul] }
      map_zero_eq_one' := by ext y; simp
      map_add_eq_mul' x y := by
        ext z
        change ψ (a * (x + y) * z) = ψ (a * x * z) * ψ (a * y * z)
        rw [mul_add, add_mul, ψ.map_add_eq_mul] }
  map_zero := by simp
  map_neg x := by simp
  map_add x y := by
    change ψ (a * (x + y) ^ 2 / 2) =
      ψ (a * x ^ 2 / 2) * ψ (a * y ^ 2 / 2) * ψ (a * x * y)
    rw [← ψ.map_add_eq_mul, ← ψ.map_add_eq_mul]
    congr 1
    have h2 : (2 : k) ≠ 0 := by norm_num
    field_simp
    ring
  norm_eq_one x := hu _

end

end OAI.RepresentationTheory.Weil.Local
