import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SymplecticBigCell
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.IntegralVacuum

/-! # Symplectic Factorization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SymplecticFactorization.CM

noncomputable section

/-! Explicit symplectic factorization over the finite adelic ring.
All factors are actual matrices, with no factorization hypothesis. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable {ι : Type*} [Fintype ι]

theorem bigCell_parameters_symmetric (A : (Matrix ι ι RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ)
    (B C D : Matrix ι ι RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
    (hg : Matrix.fromBlocks A.val B C D ∈ Matrix.symplecticGroup ι RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (C * (A⁻¹).val).IsSymm ∧ ((A⁻¹).val * B).IsSymm := by
  have hac := (SymplecticGroup.fromBlocks_mem_iff.mp hg).1
  have hab := (SymplecticGroup.fromBlocks_mem_iff.mp
    (show Matrix.fromBlocks A.val.transpose C.transpose B.transpose D.transpose ∈
      Matrix.symplecticGroup ι RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf from by
        simpa only [Matrix.fromBlocks_transpose] using SymplecticGroup.transpose_mem hg)).1
  simp only [Matrix.transpose_transpose] at hab
  constructor
  · change (C * (A⁻¹).val).transpose = C * (A⁻¹).val
    have h := congrArg (fun M => (A⁻¹).val.transpose * M * (A⁻¹).val) hac
    simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.transpose_one, one_mul] at h
    simpa only [Matrix.transpose_mul, Matrix.mul_assoc, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, mul_one] using h.symm
  · change ((A⁻¹).val * B).transpose = (A⁻¹).val * B
    have h := congrArg (fun M => (A⁻¹).val * M * (A⁻¹).val.transpose) hab
    simp only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_mul] at h
    simpa only [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.transpose_mul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one,
      mul_one] using h

theorem bigCell_factorization (A : (Matrix ι ι RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ)
    (B C D : Matrix ι ι RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
    (hg : Matrix.fromBlocks A.val B C D ∈ Matrix.symplecticGroup ι RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (⟨Matrix.fromBlocks A.val B C D, hg⟩ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp ι RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) =
      IntegralVacuum.CM.LowerBare.lower (C * (A⁻¹).val) (bigCell_parameters_symmetric A B C D hg).1 *
        RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringLevi A * RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper ((A⁻¹).val * B) (bigCell_parameters_symmetric A B C D hg).2 := by
  have hL := (bigCell_parameters_symmetric A B C D hg).1
  have had := (SymplecticGroup.fromBlocks_mem_iff.mp hg).2.2
  have hD : D = C * (A⁻¹).val * B + (A⁻¹).val.transpose := by
    have h := congrArg (fun M => (A⁻¹).val.transpose * M) had
    simp only [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.transpose_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one,
      one_mul, mul_one] at h
    rw [hL.eq] at h
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  apply Subtype.ext
  change Matrix.fromBlocks A.val B C D =
    Matrix.fromBlocks 1 0 (C * (A⁻¹).val) 1 *
      Matrix.fromBlocks A.val 0 0 (A⁻¹).val.transpose *
        Matrix.fromBlocks 1 ((A⁻¹).val * B) 0 1
  simp only [Matrix.fromBlocks_multiply, one_mul, mul_one, zero_mul, mul_zero,
    zero_add, add_zero]
  have hC : C * (A⁻¹).val * A.val = C := by
    rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have hB : A.val * ((A⁻¹).val * B) = B := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  rw [hC, hB, hD, Matrix.mul_assoc C (A⁻¹).val B]

theorem upper_cancel (B : Matrix ι ι RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) :
    RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper (-B) hB.neg * RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper B hB = 1 := by
  apply Subtype.ext
  change Matrix.fromBlocks 1 (-B) 0 1 * Matrix.fromBlocks 1 B 0 1 = 1
  simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem exists_factorization (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp ι RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    ∃ (X : Matrix ι ι RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hX : X.IsSymm) (A : (Matrix ι ι RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ)
      (C : Matrix ι ι RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hC : C.IsSymm) (D : Matrix ι ι RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hD : D.IsSymm),
      g = RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper (-X) hX.neg * IntegralVacuum.CM.LowerBare.lower C hC * RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringLevi A * RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper D hD := by
  obtain ⟨X, hX, hdet⟩ := SymplecticBigCell.CM.exists_big_cell g
  let f := RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper X hX * g
  have hdet' : IsUnit f.val.toBlocks₁₁.det := by
    change IsUnit (((RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper X hX).val * g.val).toBlocks₁₁).det
    rw [← Matrix.fromBlocks_toBlocks g.val]
    simpa [RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper, Matrix.fromBlocks_multiply] using hdet
  obtain ⟨A, hA⟩ := (Matrix.isUnit_iff_isUnit_det f.val.toBlocks₁₁).mpr hdet'
  have hmatrix : Matrix.fromBlocks A.val f.val.toBlocks₁₂ f.val.toBlocks₂₁ f.val.toBlocks₂₂ = f.val := by
    rw [hA, Matrix.fromBlocks_toBlocks]
  have hs : Matrix.fromBlocks A.val f.val.toBlocks₁₂ f.val.toBlocks₂₁ f.val.toBlocks₂₂ ∈ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp ι RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf := by
    rw [hmatrix]
    exact f.property
  have hC := (bigCell_parameters_symmetric A _ _ _ hs).1
  have hD := (bigCell_parameters_symmetric A _ _ _ hs).2
  refine ⟨X, hX, A, _, hC, _, hD, ?_⟩
  have hf : (⟨Matrix.fromBlocks A.val f.val.toBlocks₁₂ f.val.toBlocks₂₁ f.val.toBlocks₂₂, hs⟩ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp ι RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) = f :=
    Subtype.ext hmatrix
  have hdec := bigCell_factorization A _ _ _ hs
  rw [hf] at hdec
  have hrec : RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper (-X) hX.neg * f = g := by
    change RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper (-X) hX.neg * (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper X hX * g) = g
    rw [← mul_assoc, upper_cancel, one_mul]
  rw [← hrec]
  conv_lhs => rw [hdec]
  simp only [mul_assoc]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SymplecticFactorization.CM
