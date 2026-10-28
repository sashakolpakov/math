import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Period Coordinate Duality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodCoordinateDuality.CM.Construction

noncomputable section

/-! Real period coordinates identify with the complex dual of a
holomorphic summand complementary to its conjugate. -/

open _root_.Matrix

variable {ι : Type} [Fintype ι]

def complexCoordinateEvaluation (P : Submodule ℂ (ι → ℂ)) :
    (ι → ℂ) →ₗ[ℂ] Module.Dual ℂ P where
  toFun r := (dotProductBilin ℂ ℂ r).comp P.subtype
  map_add' r s := by
    ext x
    exact add_dotProduct r s x.val
  map_smul' z r := by
    ext x
    exact smul_dotProduct z r x.val

def realCoordinateCast : (ι → ℝ) →ₗ[ℝ] (ι → ℂ) :=
  LinearMap.pi (fun i => Complex.ofRealCLM.toLinearMap.comp (LinearMap.proj i))

def realPeriodEvaluation (P : Submodule ℂ (ι → ℂ)) :
    (ι → ℝ) →ₗ[ℝ] Module.Dual ℂ P :=
  ((complexCoordinateEvaluation P).restrictScalars ℝ).comp realCoordinateCast

theorem realPeriodEvaluation_apply (P : Submodule ℂ (ι → ℂ))
    (r : ι → ℝ) (x : P) : realPeriodEvaluation P r x = ∑ i, (r i : ℂ) * x.val i := rfl

def coordinateConjugateEquiv (P Q : Submodule ℂ (ι → ℂ))
    (hconj : ∀ x : ι → ℂ, star x ∈ Q ↔ x ∈ P) : P ≃ₗ[ℝ] Q where
  toFun x := ⟨star x.val, (hconj x.val).mpr x.property⟩
  invFun x := ⟨star x.val, (hconj (star x.val)).mp (by simp)⟩
  left_inv x := Subtype.ext (star_star x.val)
  right_inv x := Subtype.ext (star_star x.val)
  map_add' x y := Subtype.ext (star_add x.val y.val)
  map_smul' r x := by
    apply Subtype.ext
    ext i
    change star (r • x.val i) = r • star (x.val i)
    simp

theorem realPeriodEvaluation_injective (P Q : Submodule ℂ (ι → ℂ))
    (hcomp : IsCompl P Q) (hconj : ∀ x : ι → ℂ, star x ∈ Q ↔ x ∈ P) :
    Function.Injective (realPeriodEvaluation P) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro r hr
  have hP (x : ι → ℂ) (hx : x ∈ P) : dotProduct (fun i => (r i : ℂ)) x = 0 :=
    LinearMap.congr_fun hr ⟨x, hx⟩
  have hQ (x : ι → ℂ) (hx : x ∈ Q) : dotProduct (fun i => (r i : ℂ)) x = 0 := by
    have hs : star x ∈ P := (hconj (star x)).mp (by simpa using hx)
    have h := congrArg star (hP (star x) hs)
    simpa [dotProduct, mul_comm] using h
  have hall (x : ι → ℂ) : dotProduct (fun i => (r i : ℂ)) x = 0 := by
    have hx : x ∈ P ⊔ Q := by rw [hcomp.sup_eq_top]; trivial
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hx
    rw [dotProduct_add, hP p hp, hQ q hq, add_zero]
  ext i
  have hi := hall (Pi.single i 1)
  have hz : (r i : ℂ) = 0 := by simpa using hi
  exact_mod_cast hz

theorem realPeriodEvaluation_finrank (P Q : Submodule ℂ (ι → ℂ))
    (hcomp : IsCompl P Q) (hconj : ∀ x : ι → ℂ, star x ∈ Q ↔ x ∈ P) :
    Module.finrank ℝ (ι → ℝ) = Module.finrank ℝ (Module.Dual ℂ P) := by
  have hPQ : Module.finrank ℝ P = Module.finrank ℝ Q :=
    (coordinateConjugateEquiv P Q hconj).finrank_eq
  have htotal := ((Submodule.prodEquivOfIsCompl P Q hcomp).restrictScalars ℝ).finrank_eq
  rw [Module.finrank_prod, finrank_real_of_complex (ι → ℂ), Module.finrank_fintype_fun_eq_card,
    ← hPQ] at htotal
  have hdual : Module.finrank ℝ (Module.Dual ℂ P) = Module.finrank ℝ P := by
    rw [finrank_real_of_complex, Subspace.dual_finrank_eq, ← finrank_real_of_complex]
  rw [Module.finrank_fintype_fun_eq_card, hdual]
  omega

def realPeriodEvaluationEquiv (P Q : Submodule ℂ (ι → ℂ))
    (hcomp : IsCompl P Q) (hconj : ∀ x : ι → ℂ, star x ∈ Q ↔ x ∈ P) :
    (ι → ℝ) ≃ₗ[ℝ] Module.Dual ℂ P :=
  LinearEquiv.ofBijective (realPeriodEvaluation P)
    ⟨realPeriodEvaluation_injective P Q hcomp hconj,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (realPeriodEvaluation_finrank P Q hcomp hconj)).mp
          (realPeriodEvaluation_injective P Q hcomp hconj)⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodCoordinateDuality.CM.Construction
