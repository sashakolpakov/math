import OAI.NumberTheory.ArithmeticGroups.Lattices.UniversalRightTranslation
import OAI.NumberTheory.ArithmeticGroups.Lattices.ExteriorLine

/-! # Exterior Character Polynomial -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ExteriorCharacterPolynomial.Construction

noncomputable section

section

/-! The scalar action on a polynomial exterior line is represented by
a single coordinate polynomial over the original field. -/

open scoped Classical

def exteriorCharacterPolynomial {k : Type} [Field k] {n r : ℕ}
    (p : Fin r → Algebraic.CoordinatePolynomial n k)
    (φ : Fin r → (Algebraic.CoordinatePolynomial n k →ₗ[k] k)) : Algebraic.CoordinatePolynomial n k :=
  (Matrix.of (fun i j => UniversalRightTranslation.Construction.polynomialMatrixCoefficient (φ j) (p i))).det

theorem evaluate_exteriorCharacterPolynomial
    {k K : Type} [Field k] [Field K] {n r : ℕ}
    (p : Fin r → Algebraic.CoordinatePolynomial n k) (φ : Fin r → (Algebraic.CoordinatePolynomial n k →ₗ[k] k))
    (ι : k →+* K) (g : Algebraic.SL n K) :
    Algebraic.evaluateMatrix ι g (exteriorCharacterPolynomial p φ) =
      (Matrix.of (fun i j => PolynomialFunctionalExtension.Construction.polynomialFunctionalMap ι (φ j)
        (PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) K) (MvPolynomial.map ι (p i))))).det := by
  unfold exteriorCharacterPolynomial
  rw [RingHom.map_det]
  congr 1
  ext i j
  exact UniversalRightTranslation.Construction.evaluate_polynomialMatrixCoefficient ι g (φ j) (p i)

theorem polynomial_dual_coordinates_extend
    {k K : Type} [Field k] [Field K] {n r : ℕ}
    (p : Fin r → Algebraic.CoordinatePolynomial n k) (φ : Fin r → (Algebraic.CoordinatePolynomial n k →ₗ[k] k))
    (hφ : ∀ i j, φ j (p i) = (1 : Matrix (Fin r) (Fin r) k) i j) (ι : k →+* K) :
    ∀ i j, PolynomialFunctionalExtension.Construction.polynomialFunctionalMap ι (φ j) (MvPolynomial.map ι (p i)) =
      (1 : Matrix (Fin r) (Fin r) K) i j := by
  intro i j
  rw [PolynomialFunctionalExtension.Construction.polynomialFunctionalMap_coefficient_map, hφ]
  simp [Matrix.one_apply]

theorem exteriorCharacterPolynomial_recovers_scalar
    {k K : Type} [Field k] [Field K] {n r : ℕ}
    (p : Fin r → Algebraic.CoordinatePolynomial n k) (φ : Fin r → (Algebraic.CoordinatePolynomial n k →ₗ[k] k))
    (hφ : ∀ i j, φ j (p i) = (1 : Matrix (Fin r) (Fin r) k) i j)
    (ι : k →+* K) (g : Algebraic.SL n K) (c : K)
    (hc : ExteriorAlgebra.ιMulti K r (fun i =>
        PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) K) (MvPolynomial.map ι (p i))) =
      c • ExteriorAlgebra.ιMulti K r (fun i => MvPolynomial.map ι (p i))) :
    Algebraic.evaluateMatrix ι g (exteriorCharacterPolynomial p φ) = c := by
  rw [evaluate_exteriorCharacterPolynomial]
  exact ExteriorLine.Construction.exterior_scalar_eq_determinant _ _ (fun j => PolynomialFunctionalExtension.Construction.polynomialFunctionalMap ι (φ j))
    (polynomial_dual_coordinates_extend p φ hφ ι) c hc

theorem exteriorCharacterPolynomial_one
    {k : Type} [Field k] {n r : ℕ}
    (p : Fin r → Algebraic.CoordinatePolynomial n k) (φ : Fin r → (Algebraic.CoordinatePolynomial n k →ₗ[k] k))
    (hφ : ∀ i j, φ j (p i) = (1 : Matrix (Fin r) (Fin r) k) i j) :
    Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (exteriorCharacterPolynomial p φ) = 1 := by
  apply exteriorCharacterPolynomial_recovers_scalar p φ hφ (RingHom.id k) 1 1
  rw [one_smul]
  congr 1
  funext i
  change PolynomialAction.Construction.rightTranslate (1 : Matrix (Fin n) (Fin n) k) (MvPolynomial.map (RingHom.id k) (p i)) = _
  rw [PolynomialAction.Construction.rightTranslate_one]
  rfl

end

/-! Scalars acting on a nonzero exterior line multiply under composition
of the matrix right-translation action. -/

open scoped Classical

theorem exterior_nonzero_of_dual_coordinates
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {r : ℕ}
    (v : Fin r → V) (φ : Fin r → Module.Dual k V)
    (hφ : ∀ i j, φ j (v i) = (1 : Matrix (Fin r) (Fin r) k) i j) :
    ExteriorAlgebra.ιMulti k r v ≠ 0 := by
  intro hv
  have he : ExteriorAlgebra.ιMulti k r v = (0 : k) • ExteriorAlgebra.ιMulti k r v := by
    rw [zero_smul, hv]
  have hh := ExteriorLine.Construction.exterior_scalar_eq_determinant v v φ hφ 0 he
  have hm : Matrix.of (fun i j => φ j (v i)) = 1 := by
    ext i j
    exact hφ i j
  rw [hm, Matrix.det_one] at hh
  exact one_ne_zero hh

theorem exterior_rightTranslate_comp
    {k : Type} [Field k] {n r : ℕ} (v : Fin r → Algebraic.CoordinatePolynomial n k) (g h : Algebraic.SL n k) :
    ExteriorAlgebra.ιMulti k r
        (fun i => PolynomialAction.Construction.rightTranslate ((g * h : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) (v i)) =
      ExteriorAlgebra.map (PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) k)).toLinearMap
        (ExteriorAlgebra.ιMulti k r
          (fun i => PolynomialAction.Construction.rightTranslate (h : Matrix (Fin n) (Fin n) k) (v i))) := by
  have he : (fun i => PolynomialAction.Construction.rightTranslate ((g * h : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) (v i)) =
      (fun i => PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) k)
        (PolynomialAction.Construction.rightTranslate (h : Matrix (Fin n) (Fin n) k) (v i))) := by
    funext i
    exact congrArg (fun f : Algebraic.CoordinatePolynomial n k →ₐ[k] Algebraic.CoordinatePolynomial n k => f (v i))
      (PolynomialAction.Construction.rightTranslate_mul (g : Matrix (Fin n) (Fin n) k) (h : Matrix (Fin n) (Fin n) k))
  exact (congrArg (ExteriorAlgebra.ιMulti k r) he).trans
    (ExteriorAlgebra.map_apply_ιMulti (PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) k)).toLinearMap
      (fun i => PolynomialAction.Construction.rightTranslate (h : Matrix (Fin n) (Fin n) k) (v i))).symm

theorem exterior_rightTranslate_scalar_mul
    {k : Type} [Field k] {n r : ℕ} (v : Fin r → Algebraic.CoordinatePolynomial n k)
    (hv : ExteriorAlgebra.ιMulti k r v ≠ 0) (g h : Algebraic.SL n k) (a b c : k)
    (hg : ExteriorAlgebra.ιMulti k r (fun i => PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) k) (v i)) =
      a • ExteriorAlgebra.ιMulti k r v)
    (hh : ExteriorAlgebra.ιMulti k r (fun i => PolynomialAction.Construction.rightTranslate (h : Matrix (Fin n) (Fin n) k) (v i)) =
      b • ExteriorAlgebra.ιMulti k r v)
    (hgh : ExteriorAlgebra.ιMulti k r
        (fun i => PolynomialAction.Construction.rightTranslate ((g * h : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) (v i)) =
      c • ExteriorAlgebra.ιMulti k r v) : c = a * b := by
  let F : ExteriorAlgebra k (Algebraic.CoordinatePolynomial n k) →ₐ[k] ExteriorAlgebra k (Algebraic.CoordinatePolynomial n k) :=
    ExteriorAlgebra.map (PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) k)).toLinearMap
  have hmap (u : Fin r → Algebraic.CoordinatePolynomial n k) :
      F (ExteriorAlgebra.ιMulti k r u) = ExteriorAlgebra.ιMulti k r
        (fun i => PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) k) (u i)) :=
    ExteriorAlgebra.map_apply_ιMulti (PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) k)).toLinearMap u
  have hcomp := exterior_rightTranslate_comp v g h
  apply smul_left_injective k hv
  calc
    c • ExteriorAlgebra.ιMulti k r v = F (b • ExteriorAlgebra.ιMulti k r v) := by
      rw [← hgh, ← hh]
      exact hcomp
    _ = b • F (ExteriorAlgebra.ιMulti k r v) := F.toLinearMap.map_smul b _
    _ = b • (a • ExteriorAlgebra.ιMulti k r v) := by rw [hmap, hg]
    _ = (a * b) • ExteriorAlgebra.ιMulti k r v := by rw [smul_smul, mul_comm b a]

theorem exteriorCharacterPolynomial_mul
    {k K : Type} [Field k] [Field K] {n r : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n)
    (p : Fin r → Algebraic.CoordinatePolynomial n k) (φ : Fin r → (Algebraic.CoordinatePolynomial n k →ₗ[k] k))
    (hφ : ∀ i j, φ j (p i) = (1 : Matrix (Fin r) (Fin r) k) i j)
    (ι : k →+* K)
    (hline : ∀ g : G.Points ι, ∃ c : K,
      ExteriorAlgebra.ιMulti K r (fun i =>
        PolynomialAction.Construction.rightTranslate (g.val : Matrix (Fin n) (Fin n) K) (MvPolynomial.map ι (p i))) =
      c • ExteriorAlgebra.ιMulti K r (fun i => MvPolynomial.map ι (p i)))
    (g h : G.Points ι) :
    Algebraic.evaluateMatrix ι (g * h).val (exteriorCharacterPolynomial p φ) =
      Algebraic.evaluateMatrix ι g.val (exteriorCharacterPolynomial p φ) *
        Algebraic.evaluateMatrix ι h.val (exteriorCharacterPolynomial p φ) := by
  have he (x : G.Points ι) :
      ExteriorAlgebra.ιMulti K r (fun i =>
        PolynomialAction.Construction.rightTranslate (x.val : Matrix (Fin n) (Fin n) K) (MvPolynomial.map ι (p i))) =
      Algebraic.evaluateMatrix ι x.val (exteriorCharacterPolynomial p φ) •
        ExteriorAlgebra.ιMulti K r (fun i => MvPolynomial.map ι (p i)) := by
    obtain ⟨c, hc⟩ := hline x
    rw [exteriorCharacterPolynomial_recovers_scalar p φ hφ ι x.val c hc]
    exact hc
  apply exterior_rightTranslate_scalar_mul _ _ g.val h.val _ _ _ (he g) (he h) (he (g * h))
  exact exterior_nonzero_of_dual_coordinates _ (fun j => PolynomialFunctionalExtension.Construction.polynomialFunctionalMap ι (φ j))
    (polynomial_dual_coordinates_extend p φ hφ ι)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ExteriorCharacterPolynomial.Construction
