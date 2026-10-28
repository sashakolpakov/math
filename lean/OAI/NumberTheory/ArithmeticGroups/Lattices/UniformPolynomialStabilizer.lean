import OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialBasisExtension

/-! # Uniform Polynomial Stabilizer -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.UniformPolynomialStabilizer.Construction

noncomputable section

/-! One polynomial subspace over the original field detects the matrix
group over every extension field. -/

open scoped Classical
open _root_.MvPolynomial

theorem coefficient_map_totalDegree_le
    {k K σ : Type*} [CommSemiring k] [CommSemiring K]
    (ι : k →+* K) (p : MvPolynomial σ k) : (MvPolynomial.map ι p).totalDegree ≤ p.totalDegree :=
  Finset.sup_mono (MvPolynomial.support_map_subset ι p)

theorem exists_uniform_polynomial_subspace_stabilizer
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) :
    ∃ d : ℕ, ∀ (K : Type) [Field K] [Algebra k K], ∀ g : Algebraic.SL n K,
      g ∈ G.subgroup K (algebraMap k K) ↔
        (PolynomialBasisExtension.Construction.polynomialSubspaceExtension (K := K) (PolynomialStabilizer.Construction.boundedVanishingSpace G d)).map
          (PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) K)).toLinearMap =
          PolynomialBasisExtension.Construction.polynomialSubspaceExtension (K := K) (PolynomialStabilizer.Construction.boundedVanishingSpace G d) := by
  obtain ⟨S, hS, hdef⟩ := VanishingIdeal.Construction.exists_finite_defining_polynomials G
  let d := S.sup MvPolynomial.totalDegree
  refine ⟨d, fun K _ _ g => ?_⟩
  let G' := BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)
  rw [PolynomialBasisExtension.Construction.boundedVanishingSpace_baseChange G hG]
  constructor
  · intro hg
    exact PolynomialStabilizer.Construction.rightTranslate_boundedVanishingSpace_eq G' d g hg
  · intro hstable
    apply (hdef K (algebraMap k K) g).mpr
    intro p hp
    have hpI : p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G := hS ▸ Ideal.subset_span hp
    have hpD : p.totalDegree ≤ d := Finset.le_sup hp
    have hpmap : MvPolynomial.map (algebraMap k K) p ∈ PolynomialStabilizer.Construction.boundedVanishingSpace G' d :=
      ⟨BaseChange.Construction.coefficient_map_mem_baseChange_vanishingIdeal G _ hpI,
        (mem_restrictTotalDegree _ _ _).mpr ((coefficient_map_totalDegree_le _ _).trans hpD)⟩
    have htrans : PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) K)
        (MvPolynomial.map (algebraMap k K) p) ∈ PolynomialStabilizer.Construction.boundedVanishingSpace G' d := by
      rw [← hstable]
      exact ⟨_, hpmap, rfl⟩
    have hzero := htrans.1 K (RingHom.id K) (1 : G'.RationalPoints)
    rw [PolynomialAction.Construction.rightTranslate_evaluate] at hzero
    have hid : Matrix.SpecialLinearGroup.map (RingHom.id K) g = g := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      rfl
    simpa only [OneMemClass.coe_one, one_mul, hid, BaseChange.Construction.evaluateMatrix_coefficient_map,
      RingHom.id_comp] using hzero

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.UniformPolynomialStabilizer.Construction
