import OAI.RepresentationTheory.Hecke.RadialDilation.RationalSymmetricGeneration
import OAI.RepresentationTheory.Hecke.RadialDilation.RingWeyl
import OAI.RepresentationTheory.Theta.Generators

/-! # Rational Unipotent Generation -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.RationalUnipotentGeneration.Realization

noncomputable section

/-! Upper and lower rational unipotents generate the rational symplectic group. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem rationalWeyl_unipotent_factorization :
    RingWeyl.Realization.ringWeyl ℚ (ι := ι) = QuadraticCommutator.Realization.ringUpper (-1) Matrix.isSymm_one.neg *
      RingWeyl.Realization.ringLower ℚ 1 Matrix.isSymm_one * QuadraticCommutator.Realization.ringUpper (-1) Matrix.isSymm_one.neg := by
  apply Subtype.ext
  change (RingWeyl.Realization.ringWeyl ℚ (ι := ι)).val =
    (QuadraticCommutator.Realization.ringUpper (-1) Matrix.isSymm_one.neg).val *
      (RingWeyl.Realization.ringLower ℚ 1 Matrix.isSymm_one).val * (QuadraticCommutator.Realization.ringUpper (-1) Matrix.isSymm_one.neg).val
  simp [RingWeyl.Realization.ringWeyl, QuadraticCommutator.Realization.ringUpper, RingWeyl.Realization.ringLower, Matrix.fromBlocks_multiply]

theorem rational_symmetric_levi_factorization (A : (Matrix ι ι ℚ)ˣ) (hA : A.val.IsSymm) :
    ∃ (hAi : (A⁻¹).val.IsSymm), QuadraticCommutator.Realization.ringLevi A * RingWeyl.Realization.ringWeyl ℚ =
      QuadraticCommutator.Realization.ringUpper (-A.val) hA.neg * RingWeyl.Realization.ringLower ℚ (A⁻¹).val hAi * QuadraticCommutator.Realization.ringUpper (-A.val) hA.neg := by
  have hi : (A⁻¹).val.IsSymm := by simpa only [Matrix.coe_units_inv] using hA.inv
  refine ⟨hi, ?_⟩
  apply Subtype.ext
  change (QuadraticCommutator.Realization.ringLevi A).val * (RingWeyl.Realization.ringWeyl ℚ).val =
    (QuadraticCommutator.Realization.ringUpper (-A.val) hA.neg).val * (RingWeyl.Realization.ringLower ℚ (A⁻¹).val hi).val *
      (QuadraticCommutator.Realization.ringUpper (-A.val) hA.neg).val
  simp [QuadraticCommutator.Realization.ringLevi, RingWeyl.Realization.ringWeyl, QuadraticCommutator.Realization.ringUpper, RingWeyl.Realization.ringLower, Matrix.fromBlocks_multiply, hA.inv.eq]

theorem rationalSp_generated_by_unipotents (H : Subgroup (Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ))
    (hU : ∀ (B : Matrix ι ι ℚ) (hB : B.IsSymm), QuadraticCommutator.Realization.ringUpper B hB ∈ H)
    (hL : ∀ (B : Matrix ι ι ℚ) (hB : B.IsSymm), RingWeyl.Realization.ringLower ℚ B hB ∈ H) : H = ⊤ := by
  have hW : RingWeyl.Realization.ringWeyl ℚ (ι := ι) ∈ H := by
    rw [rationalWeyl_unipotent_factorization]
    exact H.mul_mem (H.mul_mem (hU _ _) (hL _ _)) (hU _ _)
  have hSym (A : (Matrix ι ι ℚ)ˣ) (hA : A.val.IsSymm) : QuadraticCommutator.Realization.ringLevi A ∈ H := by
    obtain ⟨hi, hfactor⟩ := rational_symmetric_levi_factorization A hA
    have h : QuadraticCommutator.Realization.ringLevi A * RingWeyl.Realization.ringWeyl ℚ ∈ H := by
      rw [hfactor]
      exact H.mul_mem (H.mul_mem (hU _ _) (hL _ hi)) (hU _ _)
    have hh := H.mul_mem h (H.inv_mem hW)
    simpa only [mul_inv_cancel_right] using hh
  have hGL : H.comap RationalSymmetricGeneration.Realization.rationalLeviHom = ⊤ := RationalSymmetricGeneration.Realization.rationalGL_generated_by_symmetric _ hSym
  apply Theta.Generators.PoissonAutomorphyConstruction.subgroup_eq_top_of_generators H hU _ hW
  intro A
  have h : A ∈ H.comap RationalSymmetricGeneration.Realization.rationalLeviHom := by rw [hGL]; trivial
  exact h

end

end OAI.RepresentationTheory.Hecke.RadialDilation.RationalUnipotentGeneration.Realization
