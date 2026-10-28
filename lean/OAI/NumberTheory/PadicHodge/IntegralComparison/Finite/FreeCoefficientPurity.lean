import OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.CoefficientEvaluation
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Free Coefficient Purity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FreeCoefficientPurity

noncomputable section

/-! Finite free coefficients in local purity. The map to the quotient dual is
canonical evaluation; a basis is used only to prove its bijectivity. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CohomologyMaps OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.CoefficientEvaluation

variable (R Q : Type u) [CommRing R] [CommRing Q] [Algebra R Q]
  (hQ : Function.Surjective (algebraMap R Q))
  (T : ModuleCat.{u} R) (n : ℕ)
  (P : ProjectiveResolution (ModuleCat.of R Q))
  (e : Quotient.CoefficientEvaluation.group R T n P ≅ ModuleCat.of R Q)

@[simp] theorem point_one : Quotient.CoefficientEvaluation.point R Q Q 1 = 𝟙 (ModuleCat.of R Q) := by
  ext q
  exact mul_one q

theorem scalar_evaluation (x : Quotient.CoefficientEvaluation.group R T n P) (q : Q) :
    Quotient.CoefficientEvaluation.dualMap R Q hQ T n P e Q P x q = q * e.hom x := by
  calc
    _ = Quotient.CoefficientEvaluation.dualMap R Q hQ T n P e Q P x (q • (1 : Q)) := by rw [smul_eq_mul, mul_one]
    _ = q * Quotient.CoefficientEvaluation.evaluation R Q T n P e Q P 1 x :=
      Quotient.CoefficientEvaluation.evaluation_smul R Q hQ T n P e Q P q 1 x
    _ = _ := by simp [Quotient.CoefficientEvaluation.evaluation, point_one]

variable (M : Type u) [AddCommGroup M] [Module Q M] [Module R M] [IsScalarTower R Q M]
  (PM : ProjectiveResolution (ModuleCat.of R M))
  {ι : Type u} [Fintype ι] (b : Module.Basis ι Q M)

def projection (i : ι) : ModuleCat.of R M ⟶ ModuleCat.of R Q :=
  ModuleCat.ofHom ((b.coord i).restrictScalars R)

theorem sum_projection_point :
    ∑ i, projection R Q M b i ≫ Quotient.CoefficientEvaluation.point R Q M (b i) = 𝟙 (ModuleCat.of R M) := by
  ext m
  simpa only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply, projection,
    ModuleCat.hom_ofHom, LinearMap.restrictScalars_apply, Quotient.CoefficientEvaluation.point, LinearMap.toSpanSingleton_apply, Module.Basis.coord_apply] using b.sum_repr m

def inverse : (M →ₗ[Q] Q) →ₗ[R] Quotient.CoefficientEvaluation.group R T n PM :=
  ∑ i, (Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) PM P (projection R Q M b i) n).hom.comp
    (e.inv.hom.comp ((LinearMap.applyₗ (R := Q) (b i)).restrictScalars R))

theorem inverse_apply (f : M →ₗ[Q] Q) :
    inverse R Q T n P e M PM b f =
      ∑ i, Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) PM P (projection R Q M b i) n (e.inv (f (b i))) := by
  simp only [inverse, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, LinearMap.applyₗ_apply_apply]

theorem right_inverse (f : M →ₗ[Q] Q) :
    Quotient.CoefficientEvaluation.dualMap R Q hQ T n P e M PM (inverse R Q T n P e M PM b f) = f := by
  ext m
  rw [inverse_apply, _root_.map_sum]
  simp only [LinearMap.sum_apply]
  have hn (i : ι) := Quotient.CoefficientEvaluation.naturality R Q hQ T n P e M PM Q P (b.coord i) (e.inv (f (b i))) m
  calc
    _ = ∑ i, Quotient.CoefficientEvaluation.dualMap R Q hQ T n P e Q P (e.inv (f (b i))) (b.coord i m) :=
      Finset.sum_congr rfl (fun i _ => hn i)
    _ = ∑ i, b.coord i m * f (b i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [scalar_evaluation]
      simp
    _ = f m := by
      have hf := congrArg f (b.sum_repr m)
      simpa only [_root_.map_sum, LinearMap.map_smul, smul_eq_mul, Module.Basis.coord_apply] using hf

theorem left_inverse (x : Quotient.CoefficientEvaluation.group R T n PM) :
    inverse R Q T n P e M PM b (Quotient.CoefficientEvaluation.dualMap R Q hQ T n P e M PM x) = x := by
  rw [inverse_apply]
  have h := congrArg (fun f => Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) PM PM f n) (sum_projection_point R Q M b)
  rw [Resolution.CohomologyMaps.map_sum, Resolution.CohomologyMaps.map_id] at h
  simp_rw [Resolution.CohomologyMaps.map_comp _ PM P PM] at h
  have hx := ConcreteCategory.congr_hom h x
  calc
    _ = ∑ i, Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) PM P (projection R Q M b i) n
        (Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) P PM (Quotient.CoefficientEvaluation.point R Q M (b i)) n x) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      change e.inv (e.hom (Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) P PM (Quotient.CoefficientEvaluation.point R Q M (b i)) n x)) = _
      exact Iso.hom_inv_id_apply e _
    _ = x := by
      simpa only [ModuleCat.comp_apply, ModuleCat.hom_sum,
        LinearMap.sum_apply, ModuleCat.id_apply] using hx

def equiv : Quotient.CoefficientEvaluation.group R T n PM ≃ₗ[R] (M →ₗ[Q] Q) :=
  { Quotient.CoefficientEvaluation.dualMap R Q hQ T n P e M PM with
    invFun := inverse R Q T n P e M PM b
    left_inv := left_inverse R Q hQ T n P e M PM b
    right_inv := right_inverse R Q hQ T n P e M PM b }

@[simp] theorem equiv_apply (x : Quotient.CoefficientEvaluation.group R T n PM) (m : M) :
    equiv R Q hQ T n P e M PM b x m = Quotient.CoefficientEvaluation.evaluation R Q T n P e M PM m x := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FreeCoefficientPurity
