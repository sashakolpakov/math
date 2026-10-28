import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PolynomialSubstitutionDegree
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PolynomialBoxDimension
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Polynomial Filtered Algebra -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PolynomialFilteredAlgebra.Construction

noncomputable section

/-! The degree filtration attached to algebra generators, with controlled changes of generators. -/

open _root_.MvPolynomial

variable {K B σ τ : Type*} [CommSemiring K] [CommSemiring B] [Algebra K B]

def polynomialFilteredPiece (v : σ → B) (n : ℕ) : Submodule K B :=
  (MvPolynomial.restrictTotalDegree σ K n).map (MvPolynomial.aeval v).toLinearMap

theorem mem_polynomialFilteredPiece (v : σ → B) (n : ℕ) (x : B) :
    x ∈ polynomialFilteredPiece (K := K) v n ↔
      ∃ p : MvPolynomial σ K, p.totalDegree ≤ n ∧ MvPolynomial.aeval v p = x := by
  simp only [polynomialFilteredPiece, Submodule.mem_map,
    MvPolynomial.mem_restrictTotalDegree, AlgHom.toLinearMap_apply]

theorem polynomialFilteredPiece_mono (v : σ → B) :
    Monotone (polynomialFilteredPiece (K := K) v) := by
  intro n m hnm x hx
  obtain ⟨p, hp, rfl⟩ := (mem_polynomialFilteredPiece v n x).mp hx
  exact (mem_polynomialFilteredPiece v m _).mpr ⟨p, hp.trans hnm, rfl⟩

theorem polynomialFilteredPiece_mul (v : σ → B) {n m : ℕ} {x y : B}
    (hx : x ∈ polynomialFilteredPiece (K := K) v n)
    (hy : y ∈ polynomialFilteredPiece (K := K) v m) :
    x * y ∈ polynomialFilteredPiece (K := K) v (n + m) := by
  obtain ⟨p, hp, rfl⟩ := (mem_polynomialFilteredPiece v n x).mp hx
  obtain ⟨q, hq, rfl⟩ := (mem_polynomialFilteredPiece v m y).mp hy
  exact (mem_polynomialFilteredPiece v (n + m) _).mpr
    ⟨p * q, (MvPolynomial.totalDegree_mul p q).trans (Nat.add_le_add hp hq), map_mul _ _ _⟩

theorem polynomialFilteredPiece_algebraMap (v : σ → B) (n : ℕ) (a : K) :
    algebraMap K B a ∈ polynomialFilteredPiece (K := K) v n :=
  (mem_polynomialFilteredPiece v n _).mpr
    ⟨MvPolynomial.C a, by simp, MvPolynomial.aeval_C _ _⟩

instance polynomialFilteredPiece_finite [Finite σ] (v : σ → B) (n : ℕ) :
    Module.Finite K (polynomialFilteredPiece (K := K) v n) := by
  unfold polynomialFilteredPiece
  infer_instance

theorem polynomialFilteredPiece_exhaustive (v : σ → B)
    (hv : Algebra.adjoin K (Set.range v) = ⊤) (x : B) :
    ∃ n : ℕ, x ∈ polynomialFilteredPiece (K := K) v n := by
  have hx : x ∈ (MvPolynomial.aeval (R := K) v).range := by
    rw [MvPolynomial.aeval_range, hv]
    trivial
  obtain ⟨p, rfl⟩ := hx
  exact ⟨p.totalDegree, (mem_polynomialFilteredPiece v _ _).mpr ⟨p, le_rfl, rfl⟩⟩

theorem polynomialFilteredPiece_change_generators (v : σ → B) (w : τ → B)
    (c : ℕ) (hw : ∀ i, w i ∈ polynomialFilteredPiece (K := K) v c) (n : ℕ) :
    polynomialFilteredPiece (K := K) w n ≤ polynomialFilteredPiece v (n * c) := by
  choose q hq hqw using fun i => (mem_polynomialFilteredPiece v c (w i)).mp (hw i)
  intro x hx
  obtain ⟨p, hp, rfl⟩ := (mem_polynomialFilteredPiece w n x).mp hx
  apply (mem_polynomialFilteredPiece v (n * c) _).mpr
  refine ⟨MvPolynomial.aeval q p, (PolynomialSubstitutionDegree.Construction.totalDegree_aeval_le q c hq p).trans
    (Nat.mul_le_mul_right c hp), ?_⟩
  rw [MvPolynomial.comp_aeval_apply]
  exact congrArg (fun z : τ → B => MvPolynomial.aeval z p) (funext hqw)

theorem polynomialFilteredPiece_exists_change_bound [Finite τ] (v : σ → B) (w : τ → B)
    (hv : Algebra.adjoin K (Set.range v) = ⊤) :
    ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ,
      polynomialFilteredPiece (K := K) w n ≤ polynomialFilteredPiece v (n * c) := by
  classical
  let := Fintype.ofFinite τ
  choose b hb using fun i => polynomialFilteredPiece_exhaustive v hv (w i)
  let c := Finset.univ.sup b + 1
  refine ⟨c, Nat.zero_lt_succ _, fun n => polynomialFilteredPiece_change_generators v w c ?_ n⟩
  intro i
  exact polynomialFilteredPiece_mono v
    ((Finset.le_sup (f := b) (Finset.mem_univ i)).trans (Nat.le_succ _)) (hb i)

theorem polynomialFilteredPiece_finrank_le
    {K B : Type*} [Field K] [CommRing B] [Algebra K B]
    (σ : Type*) [Fintype σ] (v : σ → B) (n : ℕ) :
    Module.finrank K (polynomialFilteredPiece (K := K) v n) ≤ (n + 1) ^ Fintype.card σ := by
  exact (Submodule.finrank_map_le (MvPolynomial.aeval v).toLinearMap
    (MvPolynomial.restrictTotalDegree σ K n)).trans
      (PolynomialBoxDimension.Construction.finrank_polynomial_restrictTotalDegree_le K σ n)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PolynomialFilteredAlgebra.Construction
