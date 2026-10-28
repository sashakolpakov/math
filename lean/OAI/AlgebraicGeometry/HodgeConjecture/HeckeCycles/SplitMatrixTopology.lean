import OAI.RepresentationTheory.Theta.Adelic.SplitUnitary

/-! # Split Matrix Topology -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.SplitMatrixTopology.CM

/-! Continuity of the explicit split quadratic matrix constructions. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra OAI.RepresentationTheory.Theta.Adelic.SplitUnitary
variable {k : Type*} [NormedField k] [CharZero k] {d : k}
  (r : k) (hr : r ^ 2 = d) (hr0 : r ≠ 0)
  {I : Type*} [Fintype I] [DecidableEq I]

theorem plus_continuous : Continuous (RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.plus r hr hr0) :=
  (RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_re d).add (continuous_const.mul (RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_im d))

theorem plusMatrix_continuous : Continuous (RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.plusMatrix (n := I) r hr hr0) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (plus_continuous r hr hr0).comp ((continuous_apply j).comp (continuous_apply i))

omit [Fintype I] [DecidableEq I] in
theorem joinMatrix_continuous :
    Continuous (fun p : Matrix I I k × Matrix I I k => RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.joinMatrix r hr hr0 p.1 p.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  rw [RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_iff]
  constructor
  · change Continuous (fun p : Matrix I I k × Matrix I I k => (p.1 i j + p.2 i j) / 2)
    fun_prop
  · change Continuous (fun p : Matrix I I k × Matrix I I k => (p.1 i j - p.2 i j) / (2 * r))
    fun_prop

omit [CharZero k] in
theorem transposeUnit_continuous : Continuous (RepresentationTheory.Theta.Adelic.SplitUnitary.transposeUnit (n := I) (k := k)) := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun A : (Matrix I I k)ˣ => A.val.transpose)
    fun_prop
  · change Continuous (fun A : (Matrix I I k)ˣ => A.inv.transpose)
    fun_prop

theorem joinUnits_continuous :
    Continuous (fun p : (Matrix I I k)ˣ × (Matrix I I k)ˣ => RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.joinUnits r hr hr0 p.1 p.2) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact (joinMatrix_continuous r hr hr0).comp
      ((Units.continuous_val.comp continuous_fst).prodMk (Units.continuous_val.comp continuous_snd))
  · exact (joinMatrix_continuous r hr hr0).comp
      ((Units.continuous_coe_inv.comp continuous_fst).prodMk (Units.continuous_coe_inv.comp continuous_snd))

theorem liftLinear_continuous (H : (Matrix I I (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) :
    Continuous (RepresentationTheory.Theta.Adelic.SplitUnitary.liftLinear r hr hr0 H) :=
  (joinUnits_continuous r hr hr0).comp (continuous_id.prodMk
    (transposeUnit_continuous.comp ((continuous_const.mul continuous_inv).mul continuous_const)))

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.SplitMatrixTopology.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.SplitMatrixTopology.CM.SpecialUnitary

/-! The split special-unitary identification preserves the actual local topology. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra
open OAI.RepresentationTheory.Theta.Adelic.SplitUnitary OAI.RepresentationTheory.Theta.Adelic.SplitUnitary.Special
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SplitMatrixTopology.CM
variable {k : Type*} [NormedField k] [CharZero k] {d : k}
  (r : k) (hr : r ^ 2 = d) (hr0 : r ≠ 0)
  {I : Type*} [Fintype I] [DecidableEq I]
  (H : (Matrix I I (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (hH : H.val.conjTranspose = H.val)

theorem forward_continuous : Continuous (RepresentationTheory.Theta.Adelic.SplitUnitary.Special.specialUnitaryEquivSL r hr hr0 H hH) := by
  apply Continuous.subtype_mk
  exact (plusMatrix_continuous r hr hr0).comp (Units.continuous_val.comp continuous_subtype_val)

theorem inverse_val (g : Matrix.SpecialLinearGroup I k) :
    ((RepresentationTheory.Theta.Adelic.SplitUnitary.Special.specialUnitaryEquivSL r hr hr0 H hH).symm g).val = RepresentationTheory.Theta.Adelic.SplitUnitary.liftLinear r hr hr0 H (Matrix.SpecialLinearGroup.toGL g) := by
  have h := RepresentationTheory.Theta.Adelic.SplitUnitary.liftLinear_recovers r hr hr0 H hH
    (RepresentationTheory.Theta.Adelic.SpecialUnitary.includeUnitary H.val ((RepresentationTheory.Theta.Adelic.SplitUnitary.Special.specialUnitaryEquivSL r hr hr0 H hH).symm g))
  have hp : RepresentationTheory.Theta.Adelic.SplitUnitary.plusUnitary r hr hr0 H (RepresentationTheory.Theta.Adelic.SpecialUnitary.includeUnitary H.val ((RepresentationTheory.Theta.Adelic.SplitUnitary.Special.specialUnitaryEquivSL r hr hr0 H hH).symm g)) =
      Matrix.SpecialLinearGroup.toGL g := by
    apply Units.ext
    exact congrArg (fun A : Matrix.SpecialLinearGroup I k => A.val)
      ((RepresentationTheory.Theta.Adelic.SplitUnitary.Special.specialUnitaryEquivSL r hr hr0 H hH).apply_symm_apply g)
  rw [hp] at h
  exact h.symm

omit [CharZero k] in
theorem toGL_continuous : Continuous (Matrix.SpecialLinearGroup.toGL (n := I) (R := k)) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_subtype_val
  · have he : (fun x : Matrix.SpecialLinearGroup I k => ((Matrix.SpecialLinearGroup.toGL x)⁻¹).val) =
        fun x => (x⁻¹).val := by
      funext x
      rw [← map_inv]
      rfl
    rw [he]
    exact continuous_subtype_val.comp continuous_inv

theorem inverse_continuous : Continuous (RepresentationTheory.Theta.Adelic.SplitUnitary.Special.specialUnitaryEquivSL r hr hr0 H hH).symm := by
  have he : (fun g => ((RepresentationTheory.Theta.Adelic.SplitUnitary.Special.specialUnitaryEquivSL r hr hr0 H hH).symm g).val) =
      fun g => RepresentationTheory.Theta.Adelic.SplitUnitary.liftLinear r hr hr0 H (Matrix.SpecialLinearGroup.toGL g) := funext (inverse_val r hr hr0 H hH)
  have hv := (liftLinear_continuous r hr hr0 H).comp (toGL_continuous (I := I) (k := k))
  change Continuous (fun g => RepresentationTheory.Theta.Adelic.SplitUnitary.liftLinear r hr hr0 H (Matrix.SpecialLinearGroup.toGL g)) at hv
  rw [← he] at hv
  exact hv.subtype_mk _

def homeomorphism : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H.val ≃ₜ Matrix.SpecialLinearGroup I k where
  toEquiv := (RepresentationTheory.Theta.Adelic.SplitUnitary.Special.specialUnitaryEquivSL r hr hr0 H hH).toEquiv
  continuous_toFun := forward_continuous r hr hr0 H hH
  continuous_invFun := inverse_continuous r hr hr0 H hH

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.SplitMatrixTopology.CM.SpecialUnitary

end

end OAI
