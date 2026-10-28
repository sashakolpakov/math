import OAI.NumberTheory.Quaternion.Arithmetic.PolynomialAdditiveCurves
import OAI.NumberTheory.ArithmeticGroups.Lattices.GeometricIrreducibility

/-! # Geometric Curve Generation -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.GeometricCurveGeneration

noncomputable section

section

/-! Polynomial curves have irreducible images in the specified geometric
Zariski topology. This uses the cofinite topology on the affine line. -/

open scoped Classical
open OAI.NumberTheory.ArithmeticGroups.Lattices.GeometricIrreducibility.Construction Set

variable {K : Type} [Field K]

def cofinitePolynomialPrime (t : CofiniteTopology K) : PrimeSpectrum (Polynomial K) :=
  ⟨RingHom.ker (Polynomial.evalRingHom (CofiniteTopology.of.symm t)), RingHom.ker_isPrime _⟩

theorem cofinite_polynomial_zero_closed (p : Polynomial K) :
    IsClosed {t : CofiniteTopology K | p.eval (CofiniteTopology.of.symm t) = 0} := by
  apply CofiniteTopology.isClosed_iff.mpr
  by_cases hp : p = 0
  · left
    simp [hp]
  · right
    exact (p.finite_setOfPred_isRoot hp).preimage CofiniteTopology.of.symm.injective.injOn

theorem continuous_cofinitePolynomialPrime : Continuous (cofinitePolynomialPrime (K := K)) := by
  apply continuous_iff_isClosed.mpr
  intro Z hZ
  obtain ⟨s, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus Z).mp hZ
  have he : cofinitePolynomialPrime ⁻¹' PrimeSpectrum.zeroLocus s =
      ⋂ p ∈ s, {t : CofiniteTopology K | p.eval (CofiniteTopology.of.symm t) = 0} := by
    ext t
    simp [PrimeSpectrum.mem_zeroLocus, cofinitePolynomialPrime, Set.subset_def]
  rw [he]
  exact isClosed_biInter fun p _ => cofinite_polynomial_zero_closed p

variable {F : Type} [Field F] {n : ℕ} (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)

theorem geometric_polynomial_curve_continuous
    (c : AlgebraicClosure F → G.GeometricPoints)
    (P : Matrix (Fin n) (Fin n) (Polynomial (AlgebraicClosure F)))
    (hP : ∀ t i j, (c t).val i j = (P i j).eval t) :
    @Continuous (CofiniteTopology (AlgebraicClosure F)) G.GeometricPoints
      inferInstance G.geometricTopology (fun t => c (CofiniteTopology.of.symm t)) := by
  let : TopologicalSpace G.GeometricPoints := G.geometricTopology
  let e := MvPolynomial.eval₂Hom Polynomial.C (fun ij : Fin n × Fin n => P ij.1 ij.2)
  have heval (t : AlgebraicClosure F) (p : ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n (AlgebraicClosure F)) :
      ArithmeticGroups.Lattices.Algebraic.evaluateMatrix (RingHom.id _) (c t).val p = (Polynomial.evalRingHom t) (e p) := by
    induction p using MvPolynomial.induction_on with
    | C a => simp [ArithmeticGroups.Lattices.Algebraic.evaluateMatrix, e]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p ij hp =>
      simp only [map_mul, hp]
      congr 1
      simpa [ArithmeticGroups.Lattices.Algebraic.evaluateMatrix, e] using hP t ij.1 ij.2
  have he : G.geometricPrime ∘ (fun t => c (CofiniteTopology.of.symm t)) =
      PrimeSpectrum.comap e ∘ cofinitePolynomialPrime := by
    funext t
    apply PrimeSpectrum.ext
    ext p
    change ArithmeticGroups.Lattices.Algebraic.evaluateMatrix (RingHom.id _) (c (CofiniteTopology.of.symm t)).val p = 0 ↔
      (Polynomial.evalRingHom (CofiniteTopology.of.symm t)) (e p) = 0
    rw [heval]
  apply continuous_induced_rng.mpr
  change Continuous (G.geometricPrime ∘ (fun t => c (CofiniteTopology.of.symm t)))
  rw [he]
  exact (PrimeSpectrum.continuous_comap e).comp continuous_cofinitePolynomialPrime

theorem geometric_polynomial_curve_irreducible [Infinite (AlgebraicClosure F)]
    (c : AlgebraicClosure F → G.GeometricPoints)
    (P : Matrix (Fin n) (Fin n) (Polynomial (AlgebraicClosure F)))
    (hP : ∀ t i j, (c t).val i j = (P i j).eval t) :
    @IsIrreducible G.GeometricPoints G.geometricTopology (Set.range c) := by
  let : TopologicalSpace G.GeometricPoints := G.geometricTopology
  have hi := (IrreducibleSpace.isIrreducible_univ (CofiniteTopology (AlgebraicClosure F))).image
    (fun t => c (CofiniteTopology.of.symm t))
    (geometric_polynomial_curve_continuous G c P hP).continuousOn
  have he : Set.range (fun t => c (CofiniteTopology.of.symm t)) = Set.range c := by
    ext g
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨CofiniteTopology.of.symm t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨CofiniteTopology.of t, rfl⟩
  simpa only [Set.image_univ, he] using hi

end

/-! Generation by additive polynomial curves over the algebraic closure
implies geometric connectedness. -/

open scoped Classical
open OAI.NumberTheory.ArithmeticGroups.Lattices.GeometricIrreducibility.Construction Set

variable {F : Type} [Field F] {n : ℕ} (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)

def geometricAdditiveCurveElements : Set G.GeometricPoints :=
  {g | ∃ (u : Multiplicative (AlgebraicClosure F) →* G.GeometricPoints)
    (P : Matrix (Fin n) (Fin n) (Polynomial (AlgebraicClosure F))),
    (∀ t i j, (u (Multiplicative.ofAdd t)).val i j = (P i j).eval t) ∧
      ∃ t, u (Multiplicative.ofAdd t) = g}

theorem geometric_connected_of_additive_curve_generation [Infinite (AlgebraicClosure F)]
    (hgen : Subgroup.closure (geometricAdditiveCurveElements G) = ⊤) :
    G.IsGeometricallyConnected := by
  let : TopologicalSpace G.GeometricPoints := G.geometricTopology
  let : SeparatelyContinuousMul G.GeometricPoints := {
    continuous_const_mul := fun {g} => ArithmeticGroups.Lattices.Zariski.Construction.geometric_left_mul_continuous G g
    continuous_mul_const := fun {g} => ArithmeticGroups.Lattices.Zariski.Construction.geometric_right_mul_continuous G g }
  let : ContinuousInv G.GeometricPoints := ⟨ArithmeticGroups.Lattices.Zariski.Construction.geometric_inv_continuous G⟩
  let C := ArithmeticGroups.Lattices.IrreducibleGroup.Construction.irreducibleIdentitySubgroup G.GeometricPoints
  have hle : Subgroup.closure (geometricAdditiveCurveElements G) ≤ C := by
    apply (Subgroup.closure_le C).mpr
    rintro g ⟨u, P, hP, t, rfl⟩
    apply ArithmeticGroups.Lattices.IrreducibleGroup.Construction.irreducible_subset_identityComponent
      (geometric_polynomial_curve_irreducible G (fun t => u (Multiplicative.ofAdd t)) P hP)
      (show (1 : G.GeometricPoints) ∈ Set.range (fun t => u (Multiplicative.ofAdd t)) from
        ⟨0, map_one u⟩)
    exact Set.mem_range_self t
  rw [hgen] at hle
  have hC : C = ⊤ := top_unique hle
  have he : irreducibleComponent (1 : G.GeometricPoints) = Set.univ :=
    congrArg (fun N : Subgroup G.GeometricPoints => (N : Set G.GeometricPoints)) hC
  have hi : IsIrreducible (Set.univ : Set G.GeometricPoints) := by
    rw [← he]
    exact isIrreducible_irreducibleComponent
  let : IrreducibleSpace G.GeometricPoints := (irreducibleSpace_def G.GeometricPoints).mpr hi
  exact inferInstanceAs (ConnectedSpace G.GeometricPoints)

theorem geometric_unipotent_mem_additive_curve_elements [CharZero F]
    (g : G.GeometricPoints)
    (hg : IsNilpotent (PolynomialGaloisNorm.matrixPointsHom G (algebraMap F (AlgebraicClosure F)) g - 1)) :
    g ∈ geometricAdditiveCurveElements G := by
  obtain ⟨P, hP⟩ := PolynomialMatrixCurves.unipotent_has_polynomial_powers
    (PolynomialGaloisNorm.matrixPointsHom G (algebraMap F (AlgebraicClosure F)) g) hg
  obtain ⟨u, hu⟩ := PolynomialAdditiveCurves.polynomial_curve_hom_of_nat_powers G (algebraMap F (AlgebraicClosure F)) P g hP
  refine ⟨u, P, ?_, 1, ?_⟩
  · intro t i j
    exact congrFun (congrFun (hu t) i) j
  · apply PolynomialGaloisNorm.matrixPointsHom_injective G (algebraMap F (AlgebraicClosure F))
    rw [hu]
    simpa only [Nat.cast_one, pow_one] using hP 1

theorem geometric_connected_of_unipotent_generation [CharZero F]
    (hgen : Subgroup.closure {g : G.GeometricPoints |
      IsNilpotent (PolynomialGaloisNorm.matrixPointsHom G (algebraMap F (AlgebraicClosure F)) g - 1)} = ⊤) :
    G.IsGeometricallyConnected := by
  apply geometric_connected_of_additive_curve_generation G
  apply top_unique
  rw [← hgen]
  exact Subgroup.closure_mono (fun g hg => geometric_unipotent_mem_additive_curve_elements G g hg)

end

end OAI.NumberTheory.Quaternion.Arithmetic.GeometricCurveGeneration
