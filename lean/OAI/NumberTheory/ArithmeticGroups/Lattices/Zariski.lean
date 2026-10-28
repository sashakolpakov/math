import OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialAction

/-! # Zariski -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Zariski.Construction

noncomputable section

/-! Polynomial maps and the specified geometric Zariski topology.
Only separate continuity of multiplication is used for algebraic groups. -/

open scoped Classical
open Set _root_.MvPolynomial _root_.Topology _root_.TopologicalSpace

variable {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)

local instance geometricPointsTopology : TopologicalSpace G.GeometricPoints := G.geometricTopology

theorem geometric_noetherian : NoetherianSpace G.GeometricPoints :=
  (show IsInducing G.geometricPrime from ⟨rfl⟩).noetherianSpace

theorem continuous_geometricPrime : Continuous G.geometricPrime := continuous_induced_dom

theorem geometric_polynomial_zero_closed (p : Algebraic.CoordinatePolynomial n (AlgebraicClosure k)) :
    IsClosed {x : G.GeometricPoints | Algebraic.evaluateMatrix (RingHom.id _) x.val p = 0} := by
  convert (PrimeSpectrum.isClosed_zeroLocus {p}).preimage (continuous_geometricPrime G) using 1
  ext x
  simp [PrimeSpectrum.mem_zeroLocus, Algebraic.MatrixAlgebraicGroup.geometricPrime]

theorem geometric_polynomial_map_continuous (f : G.GeometricPoints → G.GeometricPoints)
    (P : Fin n × Fin n → Algebraic.CoordinatePolynomial n (AlgebraicClosure k))
    (hP : ∀ x i j, (f x).val i j = Algebraic.evaluateMatrix (RingHom.id _) x.val (P (i, j))) :
    Continuous f := by
  have heval (x : G.GeometricPoints) (p : Algebraic.CoordinatePolynomial n (AlgebraicClosure k)) :
      Algebraic.evaluateMatrix (RingHom.id _) (f x).val p =
        Algebraic.evaluateMatrix (RingHom.id _) x.val (aeval P p) := by
    induction p using MvPolynomial.induction_on with
    | C c => simp [Algebraic.evaluateMatrix]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p ij hp =>
        rcases ij with ⟨i, j⟩
        simp only [map_mul, hp, aeval_X]
        rw [show Algebraic.evaluateMatrix (RingHom.id _) (f x).val (X (i, j)) = (f x).val i j from
          by simp [Algebraic.evaluateMatrix],
          hP]
  have hprime : G.geometricPrime ∘ f =
      PrimeSpectrum.comap (aeval P).toRingHom ∘ G.geometricPrime := by
    funext x
    apply PrimeSpectrum.ext
    ext p
    change Algebraic.evaluateMatrix (RingHom.id _) (f x).val p = 0 ↔
      Algebraic.evaluateMatrix (RingHom.id _) x.val (aeval P p) = 0
    rw [heval]
  apply continuous_induced_rng.mpr
  change Continuous (G.geometricPrime ∘ f)
  rw [hprime]
  exact (PrimeSpectrum.continuous_comap _).comp (continuous_geometricPrime G)

theorem geometric_right_mul_continuous (g : G.GeometricPoints) :
    Continuous (fun x : G.GeometricPoints => x * g) := by
  apply geometric_polynomial_map_continuous G _
    (fun ij => ∑ l, X (ij.1, l) * C (g.val l ij.2))
  intro x i j
  simp [Algebraic.evaluateMatrix, Matrix.mul_apply]

theorem geometric_left_mul_continuous (g : G.GeometricPoints) :
    Continuous (fun x : G.GeometricPoints => g * x) := by
  apply geometric_polynomial_map_continuous G _
    (fun ij => ∑ l, C (g.val ij.1 l) * X (l, ij.2))
  intro x i j
  simp [Algebraic.evaluateMatrix, Matrix.mul_apply]

theorem geometric_inv_continuous : Continuous (Inv.inv : G.GeometricPoints → G.GeometricPoints) := by
  let Xmat : Matrix (Fin n) (Fin n) (Algebraic.CoordinatePolynomial n (AlgebraicClosure k)) :=
    fun i j => X (i, j)
  apply geometric_polynomial_map_continuous G _ (fun ij => Xmat.adjugate ij.1 ij.2)
  intro x i j
  have heval := congrArg (fun M : Matrix (Fin n) (Fin n) (AlgebraicClosure k) => M i j)
    ((Algebraic.evaluateMatrix (RingHom.id _) x.val).map_adjugate Xmat)
  have hX : (Algebraic.evaluateMatrix (RingHom.id _) x.val).mapMatrix Xmat = x.val := by
    ext a b
    change Algebraic.evaluateMatrix (RingHom.id _) x.val (X (a, b)) = x.val a b
    simp [Algebraic.evaluateMatrix]
  rw [hX] at heval
  exact heval.symm

theorem geometric_commuting_closed (g : G.GeometricPoints) :
    IsClosed {x : G.GeometricPoints | x * g = g * x} := by
  let P : Fin n → Fin n → Algebraic.CoordinatePolynomial n (AlgebraicClosure k) := fun i j =>
    (∑ l, X (i, l) * C (g.val l j)) - (∑ l, C (g.val i l) * X (l, j))
  have hset : {x : G.GeometricPoints | x * g = g * x} =
      ⋂ i, ⋂ j, {x : G.GeometricPoints | Algebraic.evaluateMatrix (RingHom.id _) x.val (P i j) = 0} := by
    ext x
    simp only [mem_iInter, mem_ofPred_eq]
    constructor
    · intro hx i j
      have he := congrArg (fun y : G.GeometricPoints => y.val i j) hx
      simpa [P, Algebraic.evaluateMatrix, Matrix.mul_apply, sub_eq_zero] using he
    · intro hx
      apply Subtype.ext
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      simpa [P, Algebraic.evaluateMatrix, Matrix.mul_apply, sub_eq_zero] using hx i j
  rw [hset]
  exact isClosed_iInter fun i => isClosed_iInter fun j => geometric_polynomial_zero_closed G (P i j)

theorem geometric_center_closed :
    IsClosed (Subgroup.center G.GeometricPoints : Set G.GeometricPoints) := by
  have hset : (Subgroup.center G.GeometricPoints : Set G.GeometricPoints) =
      ⋂ g : G.GeometricPoints, {x : G.GeometricPoints | x * g = g * x} := by
    ext x
    simp only [SetLike.mem_coe, Subgroup.mem_center_iff, mem_iInter, mem_ofPred_eq]
    exact forall_congr' fun g => eq_comm
  rw [hset]
  exact isClosed_iInter (geometric_commuting_closed G)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Zariski.Construction
