import OAI.RepresentationTheory.Theta.Adelic.SplitUnitary

/-! # Split Inverse Continuous -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SplitInverseContinuous.Approximation

noncomputable section

/-! Continuity of the explicit inverse from SL to the split special unitary group. -/

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra
open OAI.RepresentationTheory.Theta.Adelic.SplitUnitary OAI.RepresentationTheory.Theta.Adelic.SplitUnitary.Special

variable {k : Type*} [NormedField k] [CharZero k] {d : k}
  (r : k) (hr : r ^ 2 = d) (hr0 : r ≠ 0)
  {n : Type*} [Fintype n] [DecidableEq n]

theorem splitAlgebra_symm_continuous : Continuous (RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.splitAlgebra r hr hr0).symm := by
  rw [RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_iff]
  constructor
  · change Continuous (fun p : k × k => (p.1 + p.2) / 2)
    fun_prop
  · change Continuous (fun p : k × k => (p.1 - p.2) / (2 * r))
    fun_prop

omit [Fintype n] [DecidableEq n] in
theorem joinMatrix_continuous :
    Continuous (fun p : Matrix n n k × Matrix n n k => RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.joinMatrix r hr hr0 p.1 p.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply (splitAlgebra_symm_continuous r hr hr0).comp
  exact ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst)).prodMk
    ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd))

theorem joinUnits_continuous :
    Continuous (fun p : (Matrix n n k)ˣ × (Matrix n n k)ˣ => RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.joinUnits r hr hr0 p.1 p.2) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact (joinMatrix_continuous r hr hr0).comp
      ((Units.continuous_val.comp continuous_fst).prodMk
        (Units.continuous_val.comp continuous_snd))
  · exact (joinMatrix_continuous r hr hr0).comp
      ((Units.continuous_coe_inv.comp continuous_fst).prodMk
        (Units.continuous_coe_inv.comp continuous_snd))

omit [CharZero k] in
theorem transposeUnit_continuous : Continuous (RepresentationTheory.Theta.Adelic.SplitUnitary.transposeUnit : (Matrix n n k)ˣ → _) := by
  apply Units.continuous_iff.mpr
  constructor <;> apply continuous_pi <;> intro i <;> apply continuous_pi <;> intro j
  · exact (continuous_apply i).comp ((continuous_apply j).comp
      (Units.continuous_val (M := Matrix n n k)))
  · exact (continuous_apply i).comp ((continuous_apply j).comp
      (Units.continuous_coe_inv (M := Matrix n n k)))

variable (H : (Matrix n n (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (hH : H.val.conjTranspose = H.val)

theorem liftLinear_continuous : Continuous (RepresentationTheory.Theta.Adelic.SplitUnitary.liftLinear r hr hr0 H) := by
  change Continuous ((fun p : (Matrix n n k)ˣ × (Matrix n n k)ˣ =>
    RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.joinUnits r hr hr0 p.1 p.2) ∘ fun A =>
      (A, RepresentationTheory.Theta.Adelic.SplitUnitary.transposeUnit (RepresentationTheory.Theta.Adelic.SplitUnitary.plusUnits r hr hr0 H * A⁻¹ * (RepresentationTheory.Theta.Adelic.SplitUnitary.plusUnits r hr hr0 H)⁻¹)))
  apply (joinUnits_continuous r hr hr0).comp
  apply continuous_id.prodMk
  apply transposeUnit_continuous.comp
  exact (continuous_const.mul continuous_inv).mul continuous_const

theorem specialUnitaryEquivSL_symm_val (g : Matrix.SpecialLinearGroup n k) :
    ((RepresentationTheory.Theta.Adelic.SplitUnitary.Special.specialUnitaryEquivSL r hr hr0 H hH).symm g).val =
      RepresentationTheory.Theta.Adelic.SplitUnitary.liftLinear r hr hr0 H (Matrix.SpecialLinearGroup.toGL g) := by
  let h : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H.val := ⟨RepresentationTheory.Theta.Adelic.SplitUnitary.liftLinear r hr hr0 H (Matrix.SpecialLinearGroup.toGL g),
    RepresentationTheory.Theta.Adelic.SplitUnitary.liftLinear_unitary r hr hr0 H hH _, RepresentationTheory.Theta.Adelic.SplitUnitary.Special.liftLinear_det_one r hr hr0 H _
      (Matrix.SpecialLinearGroup.coeToGL_det g)⟩
  have hh : RepresentationTheory.Theta.Adelic.SplitUnitary.Special.specialUnitaryEquivSL r hr hr0 H hH h = g := by
    apply Subtype.ext
    exact RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.plusMatrix_join r hr hr0 _ _
  have he : (RepresentationTheory.Theta.Adelic.SplitUnitary.Special.specialUnitaryEquivSL r hr hr0 H hH).symm g = h :=
    (RepresentationTheory.Theta.Adelic.SplitUnitary.Special.specialUnitaryEquivSL r hr hr0 H hH).injective
      ((RepresentationTheory.Theta.Adelic.SplitUnitary.Special.specialUnitaryEquivSL r hr hr0 H hH).apply_symm_apply g |>.trans hh.symm)
  exact congrArg Subtype.val he

theorem specialUnitaryEquivSL_symm_continuous :
    Continuous (RepresentationTheory.Theta.Adelic.SplitUnitary.Special.specialUnitaryEquivSL r hr hr0 H hH).symm := by
  apply continuous_induced_rng.mpr
  change Continuous (fun g => ((RepresentationTheory.Theta.Adelic.SplitUnitary.Special.specialUnitaryEquivSL r hr hr0 H hH).symm g).val)
  have he : (fun g => ((RepresentationTheory.Theta.Adelic.SplitUnitary.Special.specialUnitaryEquivSL r hr hr0 H hH).symm g).val) =
      fun g => RepresentationTheory.Theta.Adelic.SplitUnitary.liftLinear r hr hr0 H (Matrix.SpecialLinearGroup.toGL g) :=
    funext (specialUnitaryEquivSL_symm_val r hr hr0 H hH)
  rw [he]
  exact (liftLinear_continuous r hr hr0 H).comp Matrix.SpecialLinearGroup.continuous_toGL

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SplitInverseContinuous.Approximation
