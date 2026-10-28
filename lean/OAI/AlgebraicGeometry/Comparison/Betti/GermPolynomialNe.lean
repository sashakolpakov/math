import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.GermMaps
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt

/-! # Germ Polynomial Ne -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.GermPolynomialNe.AnalyticLocal

noncomputable section

section

/-! Polynomials with actual holomorphic coefficient germs evaluate in the
local ring with one extra coordinate, preserving their concrete families. -/

open Set Filter _root_.Polynomial
open scoped _root_.Topology BigOperators

open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def coordinateGerm (x : E) (c : ℂ) : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, c) :=
  ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.ofFunction (x, c) Prod.snd isOpen_univ (mem_univ _) differentiable_snd.differentiableOn

def polynomialEvaluationGerm (x : E) (c : ℂ) : (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x)[X] →+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, c) :=
  Polynomial.eval₂RingHom (Holomorphic.GermMaps.AnalyticLocal.holomorphicComposition Prod.fst differentiable_fst (x, c)) (coordinateGerm x c)

theorem polynomialEvaluationGerm_monomial (x : E) (c : ℂ) (f : E → ℂ) {U : Set E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : DifferentiableOn ℂ f U) (k : ℕ) :
    (polynomialEvaluationGerm x c (monomial k (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.ofFunction x f hU hx hf))).val =
      ((fun p : E × ℂ => f p.1 * p.2 ^ k) : Germ (𝓝 (x, c)) ℂ) := by
  change (Polynomial.eval₂ (Holomorphic.GermMaps.AnalyticLocal.holomorphicComposition Prod.fst differentiable_fst (x, c))
    (coordinateGerm x c) (monomial k (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.ofFunction x f hU hx hf))).val = _
  rw [eval₂_monomial]
  rfl

theorem polynomialEvaluationGerm_family (x : E) (c : ℂ) (P : E → ℂ[X]) (d : ℕ) {U : Set E}
    (hU : IsOpen U) (hx : x ∈ U)
    (hcoeff : ∀ k : ℕ, DifferentiableOn ℂ (fun y => (P y).coeff k) U)
    (hdegree : ∀ y ∈ U, (P y).natDegree ≤ d) :
    (polynomialEvaluationGerm x c (ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs.polynomialOfFamily x P d hU hx hcoeff)).val =
      ((fun p : E × ℂ => (P p.1).eval p.2) : Germ (𝓝 (x, c)) ℂ) := by
  let e := (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.holomorphicGerms (x, c)).subtype.comp (polynomialEvaluationGerm x c)
  change e (ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs.polynomialOfFamily x P d hU hx hcoeff) = _
  unfold ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs.polynomialOfFamily
  rw [map_sum]
  change (∑ k ∈ Finset.range (d + 1),
    (polynomialEvaluationGerm x c (monomial k
      (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.ofFunction x (fun y => (P y).coeff k) hU hx (hcoeff k)))).val) = _
  simp only [polynomialEvaluationGerm_monomial]
  rw [← Germ.coe_sum]
  apply Germ.coe_eq.mpr
  filter_upwards [(hU.prod isOpen_univ).mem_nhds (show (x, c) ∈ U ×ˢ univ from ⟨hx, mem_univ c⟩)] with p hp
  simp only [Finset.sum_apply]
  exact (eval_eq_sum_range' (lt_of_le_of_lt (hdegree p.1 hp.1) (Nat.lt_succ_self d)) p.2).symm

end

section

/-! Evaluation on a coordinate slice splits the inclusion of parameter germs. -/

open Set Filter
open scoped _root_.Topology

open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def sliceEvaluation (x : E) (c : ℂ) : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, c) →+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x :=
  Holomorphic.GermMaps.AnalyticLocal.holomorphicComposition (fun y : E => (y, c))
    (differentiable_id.prodMk (differentiable_const c)) x

def parameterInclusion (x : E) (c : ℂ) : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x →+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, c) :=
  Holomorphic.GermMaps.AnalyticLocal.holomorphicComposition Prod.fst differentiable_fst (x, c)

theorem sliceEvaluation_parameterInclusion (x : E) (c : ℂ) :
    (sliceEvaluation x c).comp (parameterInclusion x c) = RingHom.id _ := by
  rw [sliceEvaluation, parameterInclusion, Holomorphic.GermMaps.AnalyticLocal.holomorphicComposition_comp]
  exact Holomorphic.GermMaps.AnalyticLocal.holomorphicComposition_id x

theorem parameterInclusion_injective (x : E) (c : ℂ) :
    Function.Injective (parameterInclusion x c) := by
  have h : Function.LeftInverse (sliceEvaluation x c) (parameterInclusion x c) :=
    fun a => DFunLike.congr_fun (sliceEvaluation_parameterInclusion x c) a
  exact h.injective

theorem sliceEvaluation_surjective (x : E) (c : ℂ) :
    Function.Surjective (sliceEvaluation x c) := by
  intro a
  exact ⟨parameterInclusion x c a,
    DFunLike.congr_fun (sliceEvaluation_parameterInclusion x c) a⟩

def centeredCoordinateGerm (x : E) (c : ℂ) : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, c) :=
  coordinateGerm x c - Holomorphic.GermMaps.AnalyticLocal.holomorphicConstantHom (x, c) c

theorem centeredCoordinateGerm_val (x : E) (c : ℂ) :
    (centeredCoordinateGerm x c).val =
      ((fun p : E × ℂ => p.2 - c) : Germ (𝓝 (x, c)) ℂ) := rfl

theorem sliceEvaluation_centeredCoordinate (x : E) (c : ℂ) :
    sliceEvaluation x c (centeredCoordinateGerm x c) = 0 := by
  apply Subtype.ext
  change ((fun _ : E => c - c) : Germ (𝓝 x) ℂ) = 0
  simp only [sub_self]
  rfl

end

/-! The centered coordinate is a nonzero element of the holomorphic
germ domain, so multiplication by it can be cancelled. -/

open Set Filter
open scoped _root_.Topology

open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem centeredCoordinateGerm_ne_zero (x : E) (c : ℂ) : centeredCoordinateGerm x c ≠ 0 := by
  intro h
  have he := congrArg Subtype.val h
  rw [centeredCoordinateGerm_val] at he
  have hp : ∀ᶠ p in 𝓝 (x, c), p.2 - c = 0 := Germ.coe_eq.mp he
  have hz : ∀ᶠ z in 𝓝 c, z = c := by
    filter_upwards [((continuous_const.prodMk continuous_id).tendsto c).eventually hp] with z hz
    exact sub_eq_zero.mp hz
  exact (infinite_of_mem_nhds c hz) (Set.finite_singleton c)

end

end OAI.AlgebraicGeometry.Comparison.Betti.GermPolynomialNe.AnalyticLocal
