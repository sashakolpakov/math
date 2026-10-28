import OAI.NumberTheory.Quaternion.Arithmetic.TangentCone

/-! # Matrix Differential -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.MatrixDifferential

noncomputable section

section

/-! The actual analytic differential of polynomial evaluation over a
nontrivially normed field, written using formal partial derivatives. -/

open scoped Classical
open _root_.MvPolynomial Set Filter _root_.Topology

variable {K σ : Type*} [NontriviallyNormedField K] [Fintype σ]

def polynomialDifferential (p : MvPolynomial σ K) (x : σ → K) : (σ → K) →L[K] K :=
  ∑ i, eval x (pderiv i p) • ContinuousLinearMap.proj i

theorem polynomialDifferential_C (a : K) (x : σ → K) :
    polynomialDifferential (C a) x = 0 := by
  ext d
  simp [polynomialDifferential]

theorem polynomialDifferential_add (p q : MvPolynomial σ K) (x : σ → K) :
    polynomialDifferential (p + q) x = polynomialDifferential p x + polynomialDifferential q x := by
  ext d
  simp [polynomialDifferential, add_mul, Finset.sum_add_distrib]

theorem polynomialDifferential_mul_X (p : MvPolynomial σ K) (i : σ) (x : σ → K) :
    polynomialDifferential (p * X i) x =
      eval x p • ContinuousLinearMap.proj i + x i • polynomialDifferential p x := by
  ext d
  simp [polynomialDifferential, pderiv_X, Pi.single_apply, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, apply_ite]
  ring_nf

theorem hasFDerivAt_polynomial_eval (p : MvPolynomial σ K) (x : σ → K) :
    HasFDerivAt (fun y => eval y p) (polynomialDifferential p x) x := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    convert! hasFDerivAt_const (𝕜 := K) a x using 1 <;> simp [polynomialDifferential_C]
  | add p q hp hq =>
    rw [polynomialDifferential_add]
    convert! hp.add hq using 1
    ext y
    simp
  | mul_X p i hp =>
    rw [polynomialDifferential_mul_X]
    convert! hp.mul (hasFDerivAt_apply i x) using 1
    ext y
    simp

theorem polynomialDifferential_annihilates_tangentCone
    (p : MvPolynomial σ K) {s : Set (σ → K)} {x d : σ → K}
    (hzero : ∀ y ∈ s, eval y p = 0) (hx : eval x p = 0)
    (hd : d ∈ tangentConeAt K s x) : polynomialDifferential p x d = 0 := by
  obtain ⟨α, l, hl, c, u, hu, hs, hcu⟩ := exists_fun_of_mem_tangentConeAt hd
  have hlim := (hasFDerivAt_polynomial_eval p x).hasFDerivWithinAt.lim hu hs hcu
  have hz : ∀ᶠ a in l, c a • (eval (x + u a) p - eval x p) = 0 := by
    filter_upwards [hs] with a ha
    rw [hzero _ ha, hx, sub_self, smul_zero]
  exact tendsto_nhds_unique_of_eventuallyEq hlim tendsto_const_nhds hz

theorem tangentSpan_le_polynomialDifferential_ker
    (p : MvPolynomial σ K) {s : Set (σ → K)} {x : σ → K}
    (hzero : ∀ y ∈ s, eval y p = 0) (hx : eval x p = 0) :
    Submodule.span K (tangentConeAt K s x) ≤ (polynomialDifferential p x).toLinearMap.ker := by
  apply Submodule.span_le.mpr
  intro d hd
  exact polynomialDifferential_annihilates_tangentCone p hzero hx hd

end

/-! Matrix tangent directions satisfy the analytic differentials of every
polynomial equation vanishing on the subgroup. -/

open scoped Classical
open Set

variable {F K : Type} [Field F] [NontriviallyNormedField K] {n : ℕ}

def matrixEntriesLinear : Matrix (Fin n) (Fin n) K →L[K] (Fin n × Fin n → K) where
  toFun X ij := X ij.1 ij.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1)

def matrixPolynomialDifferential (p : ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n K)
    (M : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K →L[K] K :=
  (polynomialDifferential p (matrixEntriesLinear M)).comp matrixEntriesLinear

theorem matrixTangentSpan_le_equation_kernel
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K) (H : Subgroup (G.Points ι))
    (p : ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n K)
    (hp : ∀ g ∈ H, MvPolynomial.eval (fun ij => g.val ij.1 ij.2) p = 0) :
    TangentCone.matrixTangentSpan G ι H ≤ (matrixPolynomialDifferential p 1).toLinearMap.ker := by
  let s : Set (Matrix (Fin n) (Fin n) K) :=
    (fun g : G.Points ι => (g.val : Matrix (Fin n) (Fin n) K)) '' (H : Set (G.Points ι))
  have hs : ∀ y ∈ matrixEntriesLinear '' s, MvPolynomial.eval y p = 0 := by
    rintro y ⟨M, ⟨g, hg, rfl⟩, rfl⟩
    exact hp g hg
  have h1 : MvPolynomial.eval (matrixEntriesLinear (1 : Matrix (Fin n) (Fin n) K)) p = 0 := by
    change MvPolynomial.eval (fun ij => (1 : Matrix (Fin n) (Fin n) K) ij.1 ij.2) p = 0
    simpa only [OneMemClass.coe_one, Matrix.SpecialLinearGroup.coe_one] using hp 1 H.one_mem
  apply Submodule.span_le.mpr
  intro X hX
  have ht := TangentCone.continuousLinearMap_mapsTo_tangentCone (matrixEntriesLinear (K := K) (n := n)) s 1 hX
  exact polynomialDifferential_annihilates_tangentCone p hs h1 ht

theorem matrixTangentSpan_satisfies_defining_equations
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K) (H : Subgroup (G.Points ι))
    (p : ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n F) (hp : p ∈ G.equations) :
    TangentCone.matrixTangentSpan G ι H ≤
      (matrixPolynomialDifferential (MvPolynomial.map ι p) 1).toLinearMap.ker := by
  apply matrixTangentSpan_le_equation_kernel
  intro g _
  have hg := (G.mem_iff K ι g.val).mp g.property p hp
  rw [MvPolynomial.eval_map]
  exact hg

end

end OAI.NumberTheory.Quaternion.Arithmetic.MatrixDifferential
