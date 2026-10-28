import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Powers
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CovectorProducts
import OAI.AlgebraicTopology.DeRham.Comparison.TopBidegree

/-! # Covector Product -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CovectorProduct.CM.Construction

noncomputable section

section

/-! Products of actual rank-one positive forms transform by the squared
absolute value of a complex determinant in top degree. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def covectorTwoProduct : (n : ℕ) → (Fin n → Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) → Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + n)
  | 0, _ => ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) 1
  | n + 1, a => AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast (by omega)
      (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (covectorTwoProduct n (fun i => a i.castSucc)) (a (Fin.last n)))

theorem covectorDegreeCast_pullback {n m : ℕ} (h : n = m)
    (a : Analysis.DifferentialForms.Manifold.Basic.FormValue F n) (f : E →L[ℝ] F) :
    AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast h (a.compContinuousLinearMap f) =
      (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast h a).compContinuousLinearMap f := by
  subst m
  rfl

theorem covectorTwoProduct_pullback (n : ℕ) (a : Fin n → Analysis.DifferentialForms.Manifold.Basic.FormValue F 2)
    (f : E →L[ℝ] F) :
    Construction.covectorTwoProduct n (fun i => (a i).compContinuousLinearMap f) =
      (Construction.covectorTwoProduct n a).compContinuousLinearMap f := by
  induction n with
  | zero => ext v; rfl
  | succ n ih =>
      rw [Construction.covectorTwoProduct, ih, AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge_pullback, covectorDegreeCast_pullback]
      rfl

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

theorem holomorphicRankOneForm_pullback (a : F →L[ℂ] ℂ) (f : E →L[ℂ] F) :
    Powers.CM.Construction.holomorphicRankOneForm (a.comp f) =
      (Powers.CM.Construction.holomorphicRankOneForm a).compContinuousLinearMap (f.restrictScalars ℝ) := by
  have h₁ : Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector E (a.comp f) =
      (Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector F a).compContinuousLinearMap (f.restrictScalars ℝ) := by
    ext v
    rfl
  have h₂ : Complex.conjCLE.toContinuousLinearMap.compContinuousAlternatingMap
      (Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector E (a.comp f)) =
      (Complex.conjCLE.toContinuousLinearMap.compContinuousAlternatingMap
        (Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector F a)).compContinuousLinearMap (f.restrictScalars ℝ) := by
    ext v
    rfl
  unfold Powers.CM.Construction.holomorphicRankOneForm
  rw [h₂, h₁, AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge_pullback]
  ext v
  rfl

def holomorphicRankOneProduct (n : ℕ) (a : Fin n → E →L[ℂ] ℂ) :
    Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + n) := Construction.covectorTwoProduct n (fun i => Powers.CM.Construction.holomorphicRankOneForm (a i))

theorem holomorphicRankOneProduct_pullback (n : ℕ) (a : Fin n → F →L[ℂ] ℂ)
    (f : E →L[ℂ] F) :
    holomorphicRankOneProduct n (fun i => (a i).comp f) =
      (holomorphicRankOneProduct n a).compContinuousLinearMap (f.restrictScalars ℝ) := by
  unfold holomorphicRankOneProduct
  simp_rw [holomorphicRankOneForm_pullback]
  exact covectorTwoProduct_pullback n _ _

theorem holomorphicRankOneProduct_det (n : ℕ)
    (b : Module.Basis (Fin (n + n)) ℝ E) (a : Fin n → E →L[ℂ] ℂ)
    (f : E →L[ℂ] E) :
    holomorphicRankOneProduct n (fun i => (a i).comp f) =
      Complex.normSq f.toLinearMap.det • holomorphicRankOneProduct n a := by
  rw [holomorphicRankOneProduct_pullback]
  ext v
  have h := AlgebraicTopology.DeRham.Comparison.TopBidegree.topAlternating_comp_apply b
    (holomorphicRankOneProduct n a).toAlternatingMap
    (f.toLinearMap.restrictScalars ℝ) v
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply] at h
  change holomorphicRankOneProduct n a (fun i => f (v i)) =
    Complex.normSq f.toLinearMap.det • holomorphicRankOneProduct n a v at h
  exact h

end

section

/-! Grouping consecutive one-covectors into actual exterior two-products. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem covectorDegreeCast_trans {n m k : ℕ} (h : n = m) (h' : m = k)
    (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast h' (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast h a) = AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast (h.trans h') a := by
  subst m k
  rfl

theorem covectorOneProduct_cast {n m : ℕ} (h : n = m) (a : ℕ → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast h (CovectorProducts.CM.Construction.covectorOneProduct n (fun i => a i)) =
      CovectorProducts.CM.Construction.covectorOneProduct m (fun i => a i) := by
  subst m
  rfl

theorem covectorOneProduct_two (n : ℕ) (a : ℕ → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast (Nat.add_assoc n 1 1)
      (CovectorProducts.CM.Construction.covectorOneProduct (n + 1 + 1) (fun i => a i)) =
      AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (CovectorProducts.CM.Construction.covectorOneProduct n (fun i => a i)) (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (a n) (a (n + 1))) := by
  change AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast _ (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge
    (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (CovectorProducts.CM.Construction.covectorOneProduct n (fun i => a i)) (a n)) (a (n + 1))) = _
  exact WedgeAssociativity.CM.Construction.covectorWedge_assoc _ _ _

theorem covectorTwoProduct_pairs (n : ℕ) (a : ℕ → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    Construction.covectorTwoProduct n (fun i => AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (a (2 * i)) (a (2 * i + 1))) =
      CovectorProducts.CM.Construction.covectorOneProduct (n + n) (fun i => a i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Construction.covectorTwoProduct]
      change AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast _ (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge
        (Construction.covectorTwoProduct n (fun i => AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (a (2 * i)) (a (2 * i + 1))))
        (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (a (2 * n)) (a (2 * n + 1)))) = _
      rw [ih, two_mul n, ← covectorOneProduct_two, covectorDegreeCast_trans,
        covectorOneProduct_cast]

theorem covectorTwoProduct_pairs_det (n : ℕ) (a : ℕ → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1)
    (v : Fin (n + n) → E) :
    Construction.covectorTwoProduct n (fun i => AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (a (2 * i)) (a (2 * i + 1))) v =
      (Matrix.of (fun (i j : Fin (n + n)) => a j (fun _ => v i))).det := by
  rw [covectorTwoProduct_pairs, CovectorProducts.CM.Construction.covectorOneProduct_det]

theorem covectorDegreeCast_smul {n m : ℕ} (h : n = m) (c : ℂ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast h (c • a) = c • AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast h a := by
  subst m
  rfl

theorem covectorTwoProduct_const_smul (n : ℕ) (c : ℂ) (a : Fin n → Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) :
    Construction.covectorTwoProduct n (fun i => c • a i) = c ^ n • Construction.covectorTwoProduct n a := by
  induction n with
  | zero => simp only [Construction.covectorTwoProduct, pow_zero, one_smul]
  | succ n ih =>
      rw [Construction.covectorTwoProduct, ih, AlgebraicTopology.Kunneth.WedgeAlgebra.Constructions.covectorWedge_smul_left, AlgebraicTopology.Kunneth.WedgeAlgebra.Constructions.covectorWedge_smul_right,
        smul_smul, covectorDegreeCast_smul, pow_succ]
      rfl

end

section

/-! Interleaved holomorphic and antiholomorphic coordinates for the
actual top exterior product of rank-one forms. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def pairedIndex (n : ℕ) : Fin 2 × Fin n ≃ Fin (n + n) :=
  (Equiv.prodComm _ _).trans (finProdFinEquiv.trans (finCongr (Nat.mul_two n)))

theorem pairedIndex_val (n : ℕ) (i : Fin 2) (j : Fin n) :
    (pairedIndex n (i, j)).val = i.val + 2 * j.val := rfl

def pairedCovector {n : ℕ} (a : Fin n → E →L[ℂ] ℂ) (j : ℕ) : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 :=
  if hj : j / 2 < n then
    if j % 2 = 0 then Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector E (a ⟨j / 2, hj⟩)
    else Complex.conjCLE.toContinuousLinearMap.compContinuousAlternatingMap
      (Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector E (a ⟨j / 2, hj⟩))
  else 0

theorem pairedCovector_even {n : ℕ} (a : Fin n → E →L[ℂ] ℂ) (i : Fin n) :
    pairedCovector a (2 * i.val) = Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector E (a i) := by
  simp [pairedCovector, i.isLt]

theorem pairedCovector_odd {n : ℕ} (a : Fin n → E →L[ℂ] ℂ) (i : Fin n) :
    pairedCovector a (2 * i.val + 1) =
      Complex.conjCLE.toContinuousLinearMap.compContinuousAlternatingMap
        (Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector E (a i)) := by
  have hd : (2 * i.val + 1) / 2 = i.val := by omega
  have hm : (2 * i.val + 1) % 2 = 1 := by omega
  simp [pairedCovector, hd, hm, i.isLt]

theorem holomorphicRankOneProduct_coordinates (n : ℕ) (a : Fin n → E →L[ℂ] ℂ) :
    holomorphicRankOneProduct n a =
      Complex.I ^ n • CovectorProducts.CM.Construction.covectorOneProduct (n + n) (fun i => pairedCovector a i) := by
  unfold holomorphicRankOneProduct Powers.CM.Construction.holomorphicRankOneForm
  rw [covectorTwoProduct_const_smul]
  congr 1
  rw [← covectorTwoProduct_pairs]
  congr 1
  funext i
  rw [pairedCovector_even, pairedCovector_odd]

def pairedVectors {n : ℕ} (b : Fin n → E) (j : Fin (n + n)) : E :=
  if ((pairedIndex n).symm j).1 = 0 then b ((pairedIndex n).symm j).2
  else Complex.I • b ((pairedIndex n).symm j).2

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem pairedVectors_even {n : ℕ} (b : Fin n → E) (i : Fin n) :
    pairedVectors b (pairedIndex n (0, i)) = b i := by
  simp [pairedVectors]

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem pairedVectors_odd {n : ℕ} (b : Fin n → E) (i : Fin n) :
    pairedVectors b (pairedIndex n (1, i)) = Complex.I • b i := by
  simp [pairedVectors]

end

section

/-! The standard product of rank-one positive forms is nonzero in every
complex dimension, with its actual normalization on a dual frame. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem pairedCovector_index_even {n : ℕ} (a : Fin n → E →L[ℂ] ℂ) (i : Fin n) :
    pairedCovector a (pairedIndex n (0, i)).val = Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector E (a i) := by
  rw [pairedIndex_val, Fin.val_zero, zero_add, pairedCovector_even]

theorem pairedCovector_index_odd {n : ℕ} (a : Fin n → E →L[ℂ] ℂ) (i : Fin n) :
    pairedCovector a (pairedIndex n (1, i)).val =
      Complex.conjCLE.toContinuousLinearMap.compContinuousAlternatingMap
        (Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector E (a i)) := by
  rw [pairedIndex_val]
  change pairedCovector a (1 + 2 * i.val) = _
  rw [Nat.add_comm, pairedCovector_odd]

theorem pairedCovector_matrix {n : ℕ} (a : Fin n → E →L[ℂ] ℂ) (b : Fin n → E)
    (hab : ∀ i j, a i (b j) = if i = j then 1 else 0) :
    (Matrix.of (fun (i j : Fin (n + n)) => pairedCovector a j (fun _ => pairedVectors b i))).submatrix
      (pairedIndex n) (pairedIndex n) =
      Matrix.blockDiagonal (fun _ : Fin n => (!![1, 1; Complex.I, -Complex.I] : Matrix (Fin 2) (Fin 2) ℂ)) := by
  ext ⟨r, i⟩ ⟨s, j⟩
  fin_cases r <;> fin_cases s <;>
    simp [Matrix.submatrix_apply, pairedCovector_index_even, pairedCovector_index_odd,
      pairedVectors_even, pairedVectors_odd, Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector_apply,
      Matrix.blockDiagonal_apply', hab, eq_comm]
  split_ifs <;> simp

theorem holomorphicRankOneProduct_dual_eval {n : ℕ} (a : Fin n → E →L[ℂ] ℂ)
    (b : Fin n → E) (hab : ∀ i j, a i (b j) = if i = j then 1 else 0) :
    holomorphicRankOneProduct n a (pairedVectors b) = (2 : ℂ) ^ n := by
  rw [holomorphicRankOneProduct_coordinates, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, CovectorProducts.CM.Construction.covectorOneProduct_det]
  rw [← Matrix.det_submatrix_equiv_self (pairedIndex n), pairedCovector_matrix a b hab,
    Matrix.det_blockDiagonal]
  simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← mul_pow]
  congr 1
  calc
    Complex.I * (-Complex.I - Complex.I) = -2 * Complex.I ^ 2 := by ring
    _ = 2 := by rw [Complex.I_sq]; ring

theorem holomorphicRankOneProduct_dual_ne_zero {n : ℕ} (a : Fin n → E →L[ℂ] ℂ)
    (b : Fin n → E) (hab : ∀ i j, a i (b j) = if i = j then 1 else 0) :
    holomorphicRankOneProduct n a ≠ 0 := by
  intro h
  have he := holomorphicRankOneProduct_dual_eval a b hab
  rw [h] at he
  change 0 = (2 : ℂ) ^ n at he
  exact (pow_ne_zero n (by norm_num : (2 : ℂ) ≠ 0)) he.symm

end

section

/-! A complex coframe supplies a nonzero reference top form. Every
product of rank-one positive forms is a nonnegative multiple of it. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def basisHolomorphicCovector {n : ℕ} (b : Module.Basis (Fin n) ℂ E) (i : Fin n) : E →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem basisHolomorphicCovector_apply {n : ℕ} (b : Module.Basis (Fin n) ℂ E)
    (i : Fin n) (x : E) : basisHolomorphicCovector b i x = b.equivFun x i := rfl

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem basisHolomorphicCovector_basis {n : ℕ} (b : Module.Basis (Fin n) ℂ E) (i j : Fin n) :
    basisHolomorphicCovector b i (b j) = if i = j then 1 else 0 := by
  simp [basisHolomorphicCovector_apply, eq_comm]

def basisCovectorEndomorphism {n : ℕ} (b : Module.Basis (Fin n) ℂ E)
    (a : Fin n → E →L[ℂ] ℂ) : E →L[ℂ] E :=
  b.equivFunL.symm.toContinuousLinearMap.comp (ContinuousLinearMap.pi a)

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem basisHolomorphicCovector_comp {n : ℕ} (b : Module.Basis (Fin n) ℂ E)
    (a : Fin n → E →L[ℂ] ℂ) (i : Fin n) :
    (basisHolomorphicCovector b i).comp (basisCovectorEndomorphism b a) = a i := by
  ext x
  change b.equivFunL (b.equivFunL.symm (fun j => a j x)) i = a i x
  rw [ContinuousLinearEquiv.apply_symm_apply]

theorem basisRankOneProduct_ne_zero {n : ℕ} (b : Module.Basis (Fin n) ℂ E) :
    holomorphicRankOneProduct n (basisHolomorphicCovector b) ≠ 0 :=
  holomorphicRankOneProduct_dual_ne_zero _ b (basisHolomorphicCovector_basis b)

theorem holomorphicRankOneProduct_reference {n : ℕ} (b : Module.Basis (Fin n) ℂ E)
    (a : Fin n → E →L[ℂ] ℂ) :
    holomorphicRankOneProduct n a =
      Complex.normSq (basisCovectorEndomorphism b a).toLinearMap.det •
        holomorphicRankOneProduct n (basisHolomorphicCovector b) := by
  have h := holomorphicRankOneProduct_det n
    ((Complex.basisOneI.smulTower b).reindex (pairedIndex n))
    (basisHolomorphicCovector b) (basisCovectorEndomorphism b a)
  simpa only [basisHolomorphicCovector_comp] using h

theorem holomorphicRankOneProduct_nonnegative_multiple {n : ℕ}
    (b : Module.Basis (Fin n) ℂ E) (a : Fin n → E →L[ℂ] ℂ) :
    ∃ c : ℝ, 0 ≤ c ∧ holomorphicRankOneProduct n a =
      c • holomorphicRankOneProduct n (basisHolomorphicCovector b) :=
  ⟨_, Complex.normSq_nonneg _, holomorphicRankOneProduct_reference b a⟩

end

section

/-! Finite sums distribute through actual exterior products. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} {p q : ℕ}

theorem covectorWedge_sum_left (s : Finset ι) (a : ι → Analysis.DifferentialForms.Manifold.Basic.FormValue E p) (b : Analysis.DifferentialForms.Manifold.Basic.FormValue E q) :
    AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (∑ i ∈ s, a i) b = ∑ i ∈ s, AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (a i) b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, AlgebraicTopology.Kunneth.WedgeAlgebra.Constructions.covectorWedge_add_left, ih]

theorem covectorWedge_sum_right (s : Finset ι) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E p) (b : ι → Analysis.DifferentialForms.Manifold.Basic.FormValue E q) :
    AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge a (∑ i ∈ s, b i) = ∑ i ∈ s, AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge a (b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, AlgebraicTopology.Kunneth.WedgeAlgebra.Constructions.covectorWedge_add_right, ih]

theorem covectorDegreeCast_sum {n m : ℕ} (h : n = m) (s : Finset ι) (a : ι → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast h (∑ i ∈ s, a i) = ∑ i ∈ s, AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast h (a i) := by
  subst m
  rfl

theorem covectorTwoProduct_sum [Fintype ι] (n : ℕ) (a : Fin n → ι → Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) :
    Construction.covectorTwoProduct n (fun i => ∑ j, a i j) =
      ∑ f : Fin n → ι, Construction.covectorTwoProduct n (fun i => a i (f i)) := by
  classical
  induction n with
  | zero => simp [Construction.covectorTwoProduct]
  | succ n ih =>
      rw [Construction.covectorTwoProduct, ih, covectorWedge_sum_left]
      simp_rw [covectorWedge_sum_right, covectorDegreeCast_sum]
      rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => ι)).sum_comp
        (fun f => Construction.covectorTwoProduct (n + 1) (fun i => a i (f i)))]
      simp only [Fintype.sum_prod_type, Fin.snocEquiv_apply, Construction.covectorTwoProduct,
        Fin.snoc_castSucc, Fin.snoc_last]
      exact Finset.sum_comm

end

section

/-! The top exterior power of the positive form from a complex coframe
is a strictly positive multiple of its reference top form. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def coframeKahlerForm {n : ℕ} (b : Module.Basis (Fin n) ℂ E) : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2 :=
  (1 / 2 : ℂ) • ∑ i, Powers.CM.Construction.holomorphicRankOneForm (basisHolomorphicCovector b i)

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem basisCovectorEndomorphism_self {n : ℕ} (b : Module.Basis (Fin n) ℂ E) :
    basisCovectorEndomorphism b (basisHolomorphicCovector b) = ContinuousLinearMap.id ℂ E := by
  ext x
  change b.equivFunL.symm (b.equivFunL x) = x
  exact b.equivFunL.symm_apply_apply x

theorem coframeKahlerForm_top_positive_multiple {n : ℕ} (b : Module.Basis (Fin n) ℂ E) :
    ∃ c : ℝ, 0 < c ∧ Construction.covectorTwoProduct n (fun _ => coframeKahlerForm b) =
      c • holomorphicRankOneProduct n (basisHolomorphicCovector b) := by
  classical
  let coeff (f : Fin n → Fin n) : ℝ :=
    Complex.normSq (basisCovectorEndomorphism b (fun i => basisHolomorphicCovector b (f i))).toLinearMap.det
  have hid : coeff id = 1 := by
    simp only [coeff, id_eq, basisCovectorEndomorphism_self]
    change Complex.normSq (LinearMap.det (LinearMap.id : E →ₗ[ℂ] E)) = 1
    simp
  have hc : 0 < ∑ f, coeff f := by
    apply Finset.sum_pos'
    · intro f _
      exact Complex.normSq_nonneg _
    · exact ⟨id, Finset.mem_univ _, by rw [hid]; norm_num⟩
  refine ⟨(1 / 2 : ℝ) ^ n * ∑ f, coeff f, mul_pos (pow_pos (by norm_num) n) hc, ?_⟩
  unfold coframeKahlerForm
  rw [covectorTwoProduct_const_smul, covectorTwoProduct_sum]
  have hp (f : Fin n → Fin n) :
      Construction.covectorTwoProduct n (fun i => Powers.CM.Construction.holomorphicRankOneForm (basisHolomorphicCovector b (f i))) =
        coeff f • holomorphicRankOneProduct n (basisHolomorphicCovector b) :=
    holomorphicRankOneProduct_reference b _
  simp_rw [hp]
  rw [← Finset.sum_smul]
  ext v
  simp only [ContinuousAlternatingMap.smul_apply, Complex.real_smul, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat, mul_assoc]

end

section

/-! A nonzero holomorphic covector can replace one coordinate of a
coframe. The resulting actual coordinate endomorphism has nonzero determinant. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem exists_basis_covector_nonzero {n : ℕ} (b : Module.Basis (Fin n) ℂ E)
    (a : E →L[ℂ] ℂ) (ha : a ≠ 0) : ∃ j, a (b j) ≠ 0 := by
  by_contra h
  push Not at h
  apply ha
  have he : a.toLinearMap = 0 := b.ext (fun j => h j)
  ext x
  exact congrArg (fun f : E →ₗ[ℂ] ℂ => f x) he

def completedCovectors {n : ℕ} (b : Module.Basis (Fin (n + 1)) ℂ E)
    (a : E →L[ℂ] ℂ) (j : Fin (n + 1)) : Fin (n + 1) → E →L[ℂ] ℂ :=
  Fin.snoc (fun i => basisHolomorphicCovector b (j.succAbove i)) a

theorem completedCovectors_separate {n : ℕ} (b : Module.Basis (Fin (n + 1)) ℂ E)
    (a : E →L[ℂ] ℂ) (j : Fin (n + 1)) (hj : a (b j) ≠ 0)
    (x : E) (hx : ∀ i, completedCovectors b a j i x = 0) : x = 0 := by
  classical
  have hcoord (i : Fin (n + 1)) (hij : i ≠ j) : basisHolomorphicCovector b i x = 0 := by
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hij
    simpa only [completedCovectors, Fin.snoc_castSucc] using hx k.castSucc
  have he : x = basisHolomorphicCovector b j x • b j := by
    calc
      x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm
      _ = basisHolomorphicCovector b j x • b j := by
        apply Finset.sum_eq_single j
        · intro i _ hij
          change basisHolomorphicCovector b i x • b i = 0
          rw [hcoord i hij, zero_smul]
        · simp
  have hz : a x = 0 := by
    simpa only [completedCovectors, Fin.snoc_last] using hx (Fin.last n)
  rw [he, map_smul, smul_eq_mul] at hz
  have hc := (mul_eq_zero.mp hz).resolve_right hj
  rw [he, hc, zero_smul]

theorem completedCovectors_det_ne_zero {n : ℕ} (b : Module.Basis (Fin (n + 1)) ℂ E)
    (a : E →L[ℂ] ℂ) (j : Fin (n + 1)) (hj : a (b j) ≠ 0) :
    (basisCovectorEndomorphism b (completedCovectors b a j)).toLinearMap.det ≠ 0 := by
  let : FiniteDimensional ℂ E := Module.Finite.of_basis b
  have hk : (basisCovectorEndomorphism b (completedCovectors b a j)).toLinearMap.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    apply completedCovectors_separate b a j hj x
    intro i
    have hi := congrArg (basisHolomorphicCovector b i) hx
    have hcomp := congrArg (fun f : E →L[ℂ] ℂ => f x)
      (basisHolomorphicCovector_comp b (completedCovectors b a j) i)
    exact hcomp.symm.trans (hi.trans (map_zero _))
  intro hz
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz) hk

end

/-! A nonzero holomorphic one-form gives a strictly positive top form
when wedged with the penultimate power of the coframe Kähler form. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def mixedCoframeCoefficient {n : ℕ} (b : Module.Basis (Fin (n + 1)) ℂ E)
    (a : E →L[ℂ] ℂ) : ℝ :=
  (1 / 2 : ℝ) ^ n * ∑ f : Fin n → Fin (n + 1),
    Complex.normSq (basisCovectorEndomorphism b
      (Fin.snoc (fun i => basisHolomorphicCovector b (f i)) a)).toLinearMap.det

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem mixedCoframeCoefficient_nonneg {n : ℕ} (b : Module.Basis (Fin (n + 1)) ℂ E)
    (a : E →L[ℂ] ℂ) : 0 ≤ mixedCoframeCoefficient b a := by
  apply mul_nonneg (pow_nonneg (by norm_num) n)
  exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem mixedCoframeCoefficient_pos {n : ℕ} (b : Module.Basis (Fin (n + 1)) ℂ E)
    (a : E →L[ℂ] ℂ) (ha : a ≠ 0) : 0 < mixedCoframeCoefficient b a := by
  obtain ⟨j, hj⟩ := exists_basis_covector_nonzero b a ha
  apply mul_pos (pow_pos (by norm_num) n)
  apply Finset.sum_pos'
  · intro f _
    exact Complex.normSq_nonneg _
  · refine ⟨j.succAbove, Finset.mem_univ _, ?_⟩
    exact Complex.normSq_pos.mpr (completedCovectors_det_ne_zero b a j hj)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
theorem covectorTwoProduct_snoc {n : ℕ} (a : Fin n → Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (c : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) :
    Construction.covectorTwoProduct (n + 1) (Fin.snoc a c) =
      AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast (by omega) (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (Construction.covectorTwoProduct n a) c) := by
  simp only [Construction.covectorTwoProduct, Fin.snoc_castSucc, Fin.snoc_last]

theorem coframeKahlerForm_mixed_power {n : ℕ} (b : Module.Basis (Fin (n + 1)) ℂ E)
    (a : E →L[ℂ] ℂ) :
    AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast (by omega : (n + n) + 2 = (n + 1) + (n + 1))
      (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (Construction.covectorTwoProduct n (fun _ => coframeKahlerForm b))
        (Powers.CM.Construction.holomorphicRankOneForm a)) =
      mixedCoframeCoefficient b a • holomorphicRankOneProduct (n + 1) (basisHolomorphicCovector b) := by
  classical
  unfold coframeKahlerForm
  rw [covectorTwoProduct_const_smul, covectorTwoProduct_sum, AlgebraicTopology.Kunneth.WedgeAlgebra.Constructions.covectorWedge_smul_left,
    covectorWedge_sum_left, covectorDegreeCast_smul, covectorDegreeCast_sum]
  have hp (f : Fin n → Fin (n + 1)) :
      AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast (by omega : (n + n) + 2 = (n + 1) + (n + 1))
        (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge
          (Construction.covectorTwoProduct n (fun i => Powers.CM.Construction.holomorphicRankOneForm (basisHolomorphicCovector b (f i))))
          (Powers.CM.Construction.holomorphicRankOneForm a)) =
      Complex.normSq (basisCovectorEndomorphism b
        (Fin.snoc (fun i => basisHolomorphicCovector b (f i)) a)).toLinearMap.det •
          holomorphicRankOneProduct (n + 1) (basisHolomorphicCovector b) := by
    rw [← covectorTwoProduct_snoc]
    have he : Fin.snoc (fun i => Powers.CM.Construction.holomorphicRankOneForm (basisHolomorphicCovector b (f i)))
        (Powers.CM.Construction.holomorphicRankOneForm a) =
        fun i : Fin (n + 1) => Powers.CM.Construction.holomorphicRankOneForm
          ((Fin.snoc (fun j => basisHolomorphicCovector b (f j)) a : Fin (n + 1) → E →L[ℂ] ℂ) i) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    rw [he]
    exact holomorphicRankOneProduct_reference b _
  simp_rw [hp]
  rw [← Finset.sum_smul]
  ext v
  simp only [mixedCoframeCoefficient, ContinuousAlternatingMap.smul_apply,
    Complex.real_smul, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, mul_assoc]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CovectorProduct.CM.Construction
