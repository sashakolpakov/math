import OAI.NumberTheory.Quaternion.Arithmetic.PrimeLocalIntegral

/-! # Log Tangent -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.LogTangent

noncomputable section

/-! The logarithm of a sufficiently small subgroup element is an actual
tangent direction over the closed prime local field. Integer prime powers
supply the sequence approaching the identity. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set Filter _root_.Topology

variable {F : Type} [Field F] [NumberField F]

theorem local_exp_parameter_mem_tangentCone (v : HeightOneSpectrum (𝓞 F))
    {A : Type*} [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A]
    [Algebra (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A]
    [IsScalarTower (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (v.adicCompletion F) A]
    (H : Submonoid A) {X : A}
    (hX : X ∈ Metric.eball 0 (NormedSpace.expSeries (v.adicCompletion F) A).radius)
    (hexp : NormedSpace.exp X ∈ H) :
    X ∈ tangentConeAt (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (H : Set A) 1 := by
  let : CharZero (v.adicCompletion F) := Algebra.charZero_of_charZero F (v.adicCompletion F)
  let p : v.adicCompletion F := LocalCompletion.residuePrime v
  have hp0 : p ≠ 0 := Nat.cast_ne_zero.mpr (LocalCompletion.residuePrime_prime v).ne_zero
  have hp : ‖p‖ < 1 := (LocalCompletion.natCast_norm_lt_one_iff v _).mpr dvd_rfl
  let c := fun j : ℕ => (p ^ j)⁻¹
  let d := fun j : ℕ => p ^ j • X
  have hd : Tendsto d atTop (𝓝 0) := by
    simpa only [zero_smul] using
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp).smul
        (tendsto_const_nhds (x := X))
  have hcd : Tendsto (fun j => c j • d j) atTop (𝓝 X) := by
    have he : (fun j => c j • d j) = fun _ : ℕ => X := by
      funext j
      simp only [c, d, smul_smul, inv_mul_cancel₀ (pow_ne_zero j hp0), one_smul]
    rw [he]
    exact tendsto_const_nhds
  have hlim := (LocalCompletion.finite_exponential_hasStrictFDerivAt v A).hasFDerivAt.hasFDerivWithinAt
    (s := univ) |>.lim hd (Eventually.of_forall fun _ => mem_univ _) hcd
  have hscaled : Tendsto (fun j => c j • (NormedSpace.exp (d j) - 1)) atTop (𝓝 X) := by
    simpa only [zero_add, NormedSpace.exp_zero, ContinuousLinearMap.id_apply] using hlim
  have hexd : Tendsto (fun j => NormedSpace.exp (d j) - 1) atTop (𝓝 (0 : A)) := by
    have h := (LocalCompletion.finite_exponential_hasStrictFDerivAt v A).continuousAt.tendsto.comp hd
    simpa only [NormedSpace.exp_zero, sub_self, Function.comp_def] using
      h.sub (tendsto_const_nhds (x := (1 : A)))
  let c₀ := fun j : ℕ => ((LocalCompletion.residuePrime v : TangentBracket.closedPrimeSubfield (v.adicCompletion F)) ^ j)⁻¹
  have hec (j : ℕ) (Y : A) : c₀ j • Y = c j • Y := by
    rw [← IsScalarTower.algebraMap_smul (v.adicCompletion F)]
    simp only [c₀, c, p, map_inv₀, map_pow, map_natCast]
  apply mem_tangentConeAt_of_seq atTop c₀ (fun j => NormedSpace.exp (d j) - 1) hexd
  · apply Eventually.of_forall
    intro j
    rw [← add_sub_assoc, add_sub_cancel_left]
    have he : d j = (LocalCompletion.residuePrime v ^ j : ℕ) • X := by
      dsimp only [d, p]
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    rw [he, PrimeLocalIntegral.finite_exp_nsmul v _ hX]
    exact H.pow_mem hexp _
  · simpa only [hec] using hscaled

end

end OAI.NumberTheory.Quaternion.Arithmetic.LogTangent
