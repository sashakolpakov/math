import OAI.NumberTheory.ArithmeticGroups.Lattices.ExponentialPolynomial
import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Action
import OAI.NumberTheory.ArithmeticGroups.Lattices.CoordinateIdeal

/-! # Exponential Integration -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ExponentialIntegration.Construction

noncomputable section

section

/-! Infinitesimal ideal preservation integrates to an actual one-parameter
subgroup over the real or complex numbers. -/

open scoped Classical _root_.Matrix.Norms.Operator _root_.Topology
open _root_.MvPolynomial NormedSpace Set Filter

variable {k : Type} [RCLike k] {n : ℕ}

theorem analytic_eq_zero_of_all_iteratedDeriv_zero [ConnectedSpace k]
    {f : k → k} (hf : ∀ t, AnalyticAt k f t)
    (hzero : ∀ r, iteratedDeriv r f 0 = 0) : f = 0 := by
  have hord : analyticOrderAt f 0 = ⊤ := by
    rw [ENat.eq_top_iff_forall_ge]
    intro r
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf 0)).mpr
      (fun i _ => hzero i)
  have hnear : f =ᶠ[𝓝 0] 0 := analyticOrderAt_eq_top.mp hord
  have hana : AnalyticOnNhd k f univ := fun t _ => hf t
  have heq := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ 0) hnear
  funext t
  exact heq (mem_univ t)

theorem iterate_infinitesimal_mem_ideal (G : Algebraic.MatrixAlgebraicGroup k n)
    {A : Matrix (Fin n) (Fin n) k} (hA : A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G)
    {p : Algebraic.CoordinatePolynomial n k} (hp : p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G) (r : ℕ) :
    (Infinitesimal.Action.Construction.rightInfinitesimal A)^[r] p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G := by
  induction r with
  | zero => exact hp
  | succ r hr =>
    rw [Function.iterate_succ_apply']
    exact (Infinitesimal.Action.Construction.mem_infinitesimalStabilizer G A).mp hA _ hr

theorem exponentialPolynomial_zero (A : Matrix (Fin n) (Fin n) k)
    (p : Algebraic.CoordinatePolynomial n k) :
    ExponentialPolynomial.Construction.exponentialPolynomial A p 0 = Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) p := by
  simp only [ExponentialPolynomial.Construction.exponentialPolynomial, zero_smul, exp_zero, Algebraic.evaluateMatrix]
  rfl

theorem exponentialPolynomial_eq_zero_of_infinitesimal [ConnectedSpace k]
    (G : Algebraic.MatrixAlgebraicGroup k n) {A : Matrix (Fin n) (Fin n) k}
    (hA : A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G)
    {p : Algebraic.CoordinatePolynomial n k} (hp : p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G) :
    ExponentialPolynomial.Construction.exponentialPolynomial A p = 0 := by
  apply analytic_eq_zero_of_all_iteratedDeriv_zero (ExponentialPolynomial.Construction.exponentialPolynomial_analyticAt A p)
  intro r
  rw [ExponentialPolynomial.Construction.exponentialPolynomial_iteratedDeriv, exponentialPolynomial_zero]
  exact iterate_infinitesimal_mem_ideal G hA hp r k (RingHom.id k) (1 : G.RationalPoints)

theorem infinitesimal_exp_det [ConnectedSpace k]
    (G : Algebraic.MatrixAlgebraicGroup k n) {A : Matrix (Fin n) (Fin n) k}
    (hA : A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G) (t : k) :
    (exp (t • A)).det = 1 := by
  have hp : CoordinateIdeal.Construction.determinantEquation k n ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G :=
    CoordinateIdeal.Construction.definingIdeal_le_vanishingIdeal G (Ideal.subset_span (mem_insert _ _))
  have he := congrFun (exponentialPolynomial_eq_zero_of_infinitesimal G hA hp) t
  change eval₂Hom (RingHom.id k) (fun ij => exp (t • A) ij.1 ij.2)
    (CoordinateIdeal.Construction.determinantEquation k n) = 0 at he
  rw [CoordinateIdeal.Construction.eval_determinantEquation] at he
  exact sub_eq_zero.mp he

def infinitesimalExponential [ConnectedSpace k]
    (G : Algebraic.MatrixAlgebraicGroup k n) (A : Infinitesimal.Action.Construction.infinitesimalStabilizer G) (t : k) : G.RationalPoints := by
  let g : Algebraic.SL n k := ⟨exp (t • A.val), infinitesimal_exp_det G A.property t⟩
  refine ⟨g, (G.mem_iff k (RingHom.id k) g).mpr ?_⟩
  intro p hp
  exact congrFun (exponentialPolynomial_eq_zero_of_infinitesimal G A.property
    (VanishingIdeal.Construction.equations_subset_vanishingIdeal G hp)) t

end

/-! The continuous one-parameter subgroup associated to an infinitesimal
matrix, and recovery of that matrix by differentiation. -/

open scoped Classical _root_.Matrix.Norms.Operator
open NormedSpace Set

variable {k : Type} [RCLike k] [ConnectedSpace k] {n : ℕ}

theorem infinitesimalExponential_zero (G : Algebraic.MatrixAlgebraicGroup k n)
    (A : Infinitesimal.Action.Construction.infinitesimalStabilizer G) : infinitesimalExponential G A 0 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  change exp (0 • A.val) = 1
  rw [zero_smul, exp_zero]

theorem infinitesimalExponential_add (G : Algebraic.MatrixAlgebraicGroup k n)
    (A : Infinitesimal.Action.Construction.infinitesimalStabilizer G) (s t : k) :
    infinitesimalExponential G A (s + t) =
      infinitesimalExponential G A s * infinitesimalExponential G A t := by
  apply Subtype.ext
  apply Subtype.ext
  change exp ((s + t) • A.val) = exp (s • A.val) * exp (t • A.val)
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl A.val).smul_left s).smul_right t)

def infinitesimalOneParameter (G : Algebraic.MatrixAlgebraicGroup k n)
    (A : Infinitesimal.Action.Construction.infinitesimalStabilizer G) : Multiplicative k →* G.RationalPoints where
  toFun t := infinitesimalExponential G A t.toAdd
  map_one' := infinitesimalExponential_zero G A
  map_mul' s t := infinitesimalExponential_add G A s.toAdd t.toAdd

theorem continuous_infinitesimalExponential (G : Algebraic.MatrixAlgebraicGroup k n)
    (A : Infinitesimal.Action.Construction.infinitesimalStabilizer G) : Continuous (infinitesimalExponential G A) := by
  have hM : Continuous (fun t : k => exp (t • A.val)) :=
    continuous_pi fun i => continuous_pi fun j =>
      continuous_iff_continuousAt.mpr fun t => (ExponentialPolynomial.Construction.matrix_exp_entry_hasDerivAt A.val t i j).continuousAt
  exact (hM.subtype_mk _).subtype_mk _

theorem infinitesimalExponential_isConnected_range (G : Algebraic.MatrixAlgebraicGroup k n)
    (A : Infinitesimal.Action.Construction.infinitesimalStabilizer G) : IsConnected (range (infinitesimalExponential G A)) :=
  isConnected_range (continuous_infinitesimalExponential G A)

theorem infinitesimalExponential_eq_one_iff (G : Algebraic.MatrixAlgebraicGroup k n)
    (A : Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    (∀ t, infinitesimalExponential G A t = 1) ↔ A = 0 := by
  constructor
  · intro h
    apply Subtype.ext
    ext i j
    have he : (fun t : k => exp (t • A.val) i j) = fun _ => (1 : Matrix (Fin n) (Fin n) k) i j := by
      funext t
      exact congrArg (fun g : G.RationalPoints => g.val i j) (h t)
    have hd := ExponentialPolynomial.Construction.matrix_exp_entry_hasDerivAt A.val 0 i j
    rw [he] at hd
    have hz := hd.unique (hasDerivAt_const 0 ((1 : Matrix (Fin n) (Fin n) k) i j))
    change A.val i j = 0
    simpa only [zero_smul, exp_zero, Matrix.one_mul] using hz
  · rintro rfl t
    apply Subtype.ext
    apply Subtype.ext
    change exp (t • (0 : Matrix (Fin n) (Fin n) k)) = 1
    rw [smul_zero, exp_zero]

theorem infinitesimalOneParameter_eq_one_iff (G : Algebraic.MatrixAlgebraicGroup k n)
    (A : Infinitesimal.Action.Construction.infinitesimalStabilizer G) : infinitesimalOneParameter G A = 1 ↔ A = 0 := by
  rw [← infinitesimalExponential_eq_one_iff]
  constructor
  · intro h t
    exact DFunLike.congr_fun h (Multiplicative.ofAdd t)
  · intro h
    apply MonoidHom.ext
    intro t
    exact h t.toAdd

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ExponentialIntegration.Construction
