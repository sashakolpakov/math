import OAI.NumberTheory.ArithmeticGroups.Lattices.OrthonormalizationContinuity
import OAI.NumberTheory.ArithmeticGroups.Lattices.GramSchmidtPositiveDiagonal
import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousEndMatrixEquiv

/-! # Operator QR Basis -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRBasis.Construction

noncomputable section

/-! A continuous orthonormal frame and positive diagonal are attached
to every invertible operator by Gram--Schmidt. -/

open InnerProductSpace
open scoped Classical

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

local instance qrBasisEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance qrBasisEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance qrBasisEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance

omit [FiniteDimensional ℝ L] in
theorem operatorFrame_linearIndependent {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g : (L →L[ℝ] L)ˣ) : LinearIndependent ℝ (fun i => g.val (b i)) :=
  b.toBasis.linearIndependent.map' (ContinuousLinearEquiv.ofUnit g).toLinearMap
    (LinearMap.ker_eq_bot.mpr (ContinuousLinearEquiv.ofUnit g).injective)

def operatorQRBasis {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (g : (L →L[ℝ] L)ˣ) :
    OrthonormalBasis (Fin m) ℝ L :=
  gramSchmidtOrthonormalBasis (Module.finrank_eq_card_basis b.toBasis) (fun i => g.val (b i))

def operatorQRDiagonal {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (g : (L →L[ℝ] L)ˣ) (i : Fin m) : ℝ :=
  ‖gramSchmidt ℝ (fun j => g.val (b j)) i‖

omit [FiniteDimensional ℝ L] in
theorem operatorQRDiagonal_pos {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g : (L →L[ℝ] L)ˣ) (i : Fin m) : 0 < operatorQRDiagonal b g i :=
  norm_pos_iff.mpr (gramSchmidt_ne_zero i (operatorFrame_linearIndependent b g))

theorem operatorQRBasis_continuous {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (i : Fin m) :
    Continuous (fun g : (L →L[ℝ] L)ˣ => operatorQRBasis b g i) :=
  OrthonormalizationContinuity.Construction.gramSchmidtOrthonormalBasis_continuous_family (Module.finrank_eq_card_basis b.toBasis)
    (fun (g : (L →L[ℝ] L)ˣ) j => g.val (b j)) (fun _ => Units.continuous_val.clm_apply continuous_const)
    (operatorFrame_linearIndependent b) i

omit [FiniteDimensional ℝ L] in
theorem operatorQRDiagonal_continuous {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (i : Fin m) :
    Continuous (fun g : (L →L[ℝ] L)ˣ => operatorQRDiagonal b g i) :=
  (GramSchmidtContinuity.Construction.gramSchmidt_continuous_family (fun (g : (L →L[ℝ] L)ˣ) j => g.val (b j))
    (fun _ => Units.continuous_val.clm_apply continuous_const) (operatorFrame_linearIndependent b) i).norm

theorem operatorQRBasis_diagonal {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g : (L →L[ℝ] L)ˣ) (i : Fin m) :
    inner ℝ (operatorQRBasis b g i) (g.val (b i)) = operatorQRDiagonal b g i := by
  have hi : gramSchmidtNormed ℝ (fun j => g.val (b j)) i ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [gramSchmidtNormed_unit_length i (operatorFrame_linearIndependent b g)]
    exact one_ne_zero
  rw [operatorQRBasis, gramSchmidtOrthonormalBasis_apply _ hi]
  exact GramSchmidtPositiveDiagonal.Construction.gramSchmidtNormed_inner_original _ (operatorFrame_linearIndependent b g) i

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRBasis.Construction
