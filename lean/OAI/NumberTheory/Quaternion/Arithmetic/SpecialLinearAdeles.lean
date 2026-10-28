import OAI.NumberTheory.Quaternion.Arithmetic.PolynomialCurveTransport
import OAI.NumberTheory.Quaternion.Arithmetic.SpecialLinear

/-! # Special Linear Adeles -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.SpecialLinearAdeles

noncomputable section

/-! An unconditional instance of the adelic curve argument: strong
approximation for the actual special-linear matrix algebraic group. -/

open scoped Classical
open _root_.Matrix _root_.Matrix.SpecialLinearGroup

def specialLinearMatrixGroup (F : Type) [Field F] (n : ℕ) : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n where
  equations := ∅
  subgroup _ _ _ := ⊤
  mem_iff _ _ _ _ := by simp

variable {F : Type} [Field F] {n : ℕ}

def specialLinearTransvectionCurve {i j : Fin n} (hij : i ≠ j) :
    PolynomialAdditiveCurves.PolynomialAdditiveCurve (specialLinearMatrixGroup F n) where
  coordinates := (1 : Matrix (Fin n) (Fin n) (Polynomial F)) + Matrix.single i j Polynomial.X
  hom K _ _ := (FiniteIndex.transvectionParameter (K := K) hij).codRestrict ⊤ (fun _ => Subgroup.mem_top _)
  coordinate_eq K _ ρ t r s := by
    change Matrix.transvection i j t r s =
      ((1 : Matrix (Fin n) (Fin n) (Polynomial F)) r s +
        (Matrix.single i j (Polynomial.X : Polynomial F)) r s).eval₂ ρ t
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply,
      Polynomial.eval₂_add]
    split_ifs <;> simp

theorem specialLinear_curve_generation [NumberField F] [Nontrivial (Fin n)] (v : LocalAdeles.Place F) :
    Subgroup.closure (PolynomialCurveTransport.groundFieldCurveElements (specialLinearMatrixGroup F n) v) = ⊤ := by
  let H := Subgroup.closure (PolynomialCurveTransport.groundFieldCurveElements (specialLinearMatrixGroup F n) v)
  apply top_unique
  intro g _
  have h (a : ArithmeticGroups.Lattices.Algebraic.SL n (LocalAdeles.Completion v)) :
      (⟨a, Subgroup.mem_top a⟩ : LocalAdeles.LocalPoints (specialLinearMatrixGroup F n) v) ∈ H := by
    apply SpecialLinear.specialLinear_transvection_induction
      (fun a => (⟨a, Subgroup.mem_top a⟩ : LocalAdeles.LocalPoints (specialLinearMatrixGroup F n) v) ∈ H)
    · intro i j hij t
      apply Subgroup.subset_closure
      exact ⟨specialLinearTransvectionCurve (F := F) hij, t, rfl⟩
    · intro a b ha hb
      exact H.mul_mem ha hb
  exact h g.val

theorem strongApproximation_specialLinear [NumberField F] [Nontrivial (Fin n)]
    (S : Finset (LocalAdeles.Place F)) (harch : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ S) :
    DenseRange (LocalAdeles.diagonalAway (specialLinearMatrixGroup F n) S) :=
  PolynomialCurveTransport.strongApproximation_of_groundField_curve_generation _ S harch
    (fun v => specialLinear_curve_generation v.val)

end

end OAI.NumberTheory.Quaternion.Arithmetic.SpecialLinearAdeles
