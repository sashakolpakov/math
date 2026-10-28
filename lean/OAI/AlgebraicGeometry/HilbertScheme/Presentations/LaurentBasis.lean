import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LaurentMonomials
import Mathlib.LinearAlgebra.Basis.Basic

/-! # Laurent Basis -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.LaurentBasis.ProjectiveCech

noncomputable section

/-!
The principal localization at a product of variables is free over the
coefficient ring, with the expected partially Laurent monomial basis.
-/

open _root_.MvPolynomial _root_.Module

universe u v

variable {σ : Type u} [Fintype σ] [DecidableEq σ]
variable (R : Type v) [CommRing R]

theorem laurentMonomial_linearIndependent (s : Finset σ) :
    LinearIndependent R (LaurentMonomials.ProjectiveCech.laurentMonomial R (s := s)) := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent]
  intro t
  let k : ℕ := ∑ a ∈ t, LaurentExponents.ProjectiveCech.denominatorBound a
  have hk (a : t) : LaurentExponents.ProjectiveCech.denominatorBound a.val ≤ k :=
    Finset.single_le_sum (f := fun a => LaurentExponents.ProjectiveCech.denominatorBound a)
      (fun _ _ => Nat.zero_le _) a.property
  let e : t → σ →₀ ℕ := fun a => LaurentExponents.ProjectiveCech.numeratorExponent a.val k
  have he : Function.Injective e := by
    intro a b h
    apply Subtype.ext
    exact LaurentExponents.ProjectiveCech.numeratorExponent_injective a.val b.val k (hk a) (hk b) h
  let f : MvPolynomial σ R →ₗ[R] LaurentMonomials.ProjectiveCech.ChartLocalization R s :=
    (IsScalarTower.toAlgHom R (MvPolynomial σ R) (LaurentMonomials.ProjectiveCech.ChartLocalization R s)).toLinearMap
  have hf : LinearMap.ker f = ⊥ :=
    LinearMap.ker_eq_bot.mpr (LaurentMonomials.ProjectiveCech.chartLocalization_injective R s)
  have hi := ((basisMonomials σ R).linearIndependent.comp e he).map' f hf
  let μ : LaurentMonomials.ProjectiveCech.ChartLocalization R s →ₗ[R] LaurentMonomials.ProjectiveCech.ChartLocalization R s :=
    LinearMap.mulLeft R (algebraMap (MvPolynomial σ R) (LaurentMonomials.ProjectiveCech.ChartLocalization R s)
      (LaurentMonomials.ProjectiveCech.inversionMonomial R s ^ k))
  apply LinearIndependent.of_comp μ
  have hμ : μ ∘ (LaurentMonomials.ProjectiveCech.laurentMonomial R ∘ (Subtype.val : t → LaurentExponents.ProjectiveCech.LaurentExponent s)) =
      f ∘ ((basisMonomials σ R) ∘ e) := by
    funext a
    exact LaurentMonomials.ProjectiveCech.laurentMonomial_clear R a.val k (hk a)
  rw [hμ]
  exact hi

def chartFractionLinearMap (s : Finset σ) (k : ℕ) :
    MvPolynomial σ R →ₗ[R] LaurentMonomials.ProjectiveCech.ChartLocalization R s :=
  (LinearMap.mulRight R (IsLocalization.mk' (LaurentMonomials.ProjectiveCech.ChartLocalization R s) 1
    (LaurentMonomials.ProjectiveCech.chartDenominator R s k))).comp
    (IsScalarTower.toAlgHom R (MvPolynomial σ R) (LaurentMonomials.ProjectiveCech.ChartLocalization R s)).toLinearMap

omit [Fintype σ] [DecidableEq σ] in
theorem chartFractionLinearMap_apply (s : Finset σ) (k : ℕ) (p : MvPolynomial σ R) :
    chartFractionLinearMap R s k p =
      IsLocalization.mk' (LaurentMonomials.ProjectiveCech.ChartLocalization R s) p (LaurentMonomials.ProjectiveCech.chartDenominator R s k) :=
  (IsLocalization.mk'_eq_mul_mk'_one (S := LaurentMonomials.ProjectiveCech.ChartLocalization R s) p
    (LaurentMonomials.ProjectiveCech.chartDenominator R s k)).symm

theorem chartFractionLinearMap_mem_span (s : Finset σ) (k : ℕ) (p : MvPolynomial σ R) :
    chartFractionLinearMap R s k p ∈ Submodule.span R (Set.range (LaurentMonomials.ProjectiveCech.laurentMonomial R (s := s))) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d r =>
    have h : monomial d r = r • monomial d (1 : R) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [h, map_smul, chartFractionLinearMap_apply, ← LaurentMonomials.ProjectiveCech.laurentMonomial_ofNumerator]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨_, rfl⟩)
  | add p q hp hq =>
    rw [map_add]
    exact Submodule.add_mem _ hp hq

theorem laurentMonomial_span (s : Finset σ) :
    Submodule.span R (Set.range (LaurentMonomials.ProjectiveCech.laurentMonomial R (s := s))) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨p, ⟨d, hd⟩, rfl⟩ :=
    IsLocalization.exists_mk'_eq (Submonoid.powers (LaurentMonomials.ProjectiveCech.inversionMonomial R s)) x
  obtain ⟨k, rfl⟩ := hd
  exact (chartFractionLinearMap_apply R s k p) ▸ chartFractionLinearMap_mem_span R s k p

def laurentBasis (s : Finset σ) : Basis (LaurentExponents.ProjectiveCech.LaurentExponent s) R (LaurentMonomials.ProjectiveCech.ChartLocalization R s) :=
  Basis.mk (laurentMonomial_linearIndependent R s) (by rw [laurentMonomial_span])

theorem laurentBasis_apply (s : Finset σ) (a : LaurentExponents.ProjectiveCech.LaurentExponent s) :
    laurentBasis R s a = LaurentMonomials.ProjectiveCech.laurentMonomial R a :=
  Basis.mk_apply _ _ _

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.LaurentBasis.ProjectiveCech
