import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.Polynomial
import OAI.NumberTheory.ArithmeticGroups.Lattices.ExteriorLattice
import OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeComparison

/-! # Exterior Vector -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.ExteriorVector.Construction

noncomputable section

/-! The uniform fixed vector can be scaled into a full, finitely
generated integral exterior lattice. Integral special-linear matrices
preserve that lattice. -/

open scoped Classical TensorProduct nonZeroDivisors

theorem integral_exterior_lattice_action_mem
    {R k : Type} [CommRing R] [Field k] [Algebra R k] [FaithfulSMul R k] {n d r : ℕ}
    (g : Matrix.SpecialLinearGroup (Fin n) R)
    {w : ⋀[k]^r (BoundedRepresentation.Construction.BoundedPolynomials k n d)}
    (hw : w ∈ ExteriorLattice.Construction.exteriorLatticeSpan (k := k)
      (Polynomial.Construction.boundedIntegralPolynomialLattice (R := R) (k := k) n d) r) :
    exteriorPower.map r
        (BoundedRepresentation.Construction.boundedPolynomialRepresentation d (Matrix.SpecialLinearGroup.map (algebraMap R k) g)).toLinearMap w ∈
      ExteriorLattice.Construction.exteriorLatticeSpan (k := k) (Polynomial.Construction.boundedIntegralPolynomialLattice (R := R) (k := k) n d) r := by
  apply ExteriorLattice.Construction.exteriorLatticeSpan_map_mem _ r _ _ hw
  intro p hp
  exact Polynomial.Construction.boundedIntegralPolynomialLattice_action_mem g hp

theorem exists_integral_uniform_exterior_vector_stabilizer
    {R k : Type} [CommRing R] [IsDomain R] [Field k] [CharZero k]
    [Algebra R k] [IsFractionRing R k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hconn : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple) :
    ∃ d r : ℕ, ∃ p : Fin r → BoundedRepresentation.Construction.BoundedPolynomials k n d, ∃ c : k,
      c ≠ 0 ∧
      c • exteriorPower.ιMulti k r p ∈ ExteriorLattice.Construction.exteriorLatticeSpan (k := k)
        (Polynomial.Construction.boundedIntegralPolynomialLattice (R := R) (k := k) n d) r ∧
      ∀ (K : Type) [Field K] [Algebra k K],
        let w := algebraMap k K c • exteriorPower.ιMulti K r
          (fun i => Finite.UniformExteriorLine.Construction.boundedCoefficientMap (K := K) (p i))
        w ≠ 0 ∧ ∀ g : Algebraic.SL n K, g ∈ G.subgroup K (algebraMap k K) ↔
          exteriorPower.map r (BoundedRepresentation.Construction.boundedPolynomialRepresentation d g).toLinearMap w = w := by
  obtain ⟨d, r, p, hp⟩ := Polynomial.Construction.exists_finite_uniform_exterior_vector_stabilizer G hconn hsemi
  let Λ := Polynomial.Construction.boundedIntegralPolynomialLattice (R := R) (k := k) n d
  let Ω := ExteriorLattice.Construction.exteriorLatticeSpan (k := k) Λ r
  have hfull : Submodule.span k (Ω : Set (⋀[k]^r (BoundedRepresentation.Construction.BoundedPolynomials k n d))) = ⊤ :=
    ExteriorLattice.Construction.exteriorLatticeSpan_full Λ (Polynomial.Construction.boundedIntegralPolynomialLattice_full n d) r
  obtain ⟨a, ha⟩ := LatticeComparison.Construction.denominator_of_full_submodule Ω hfull (exteriorPower.ιMulti k r p)
  let c : k := algebraMap R k (a : R)
  have hc : c ≠ 0 := fun h => nonZeroDivisors.ne_zero a.property
    ((IsFractionRing.injective R k) (h.trans (map_zero (algebraMap R k)).symm))
  refine ⟨d, r, p, c, hc, ?_, fun K _ _ => ?_⟩
  · change algebraMap R k (a : R) • exteriorPower.ιMulti k r p ∈ Ω
    simpa only [IsScalarTower.algebraMap_smul] using ha
  · have hcK : algebraMap k K c ≠ 0 := fun h => hc ((algebraMap k K).injective
      (h.trans (map_zero (algebraMap k K)).symm))
    refine ⟨smul_ne_zero hcK (ExteriorLine.Construction.exteriorPower_ιMulti_ne_zero (hp K).1), fun g => ?_⟩
    rw [(hp K).2 g, map_smul, smul_right_inj hcK]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.ExteriorVector.Construction
