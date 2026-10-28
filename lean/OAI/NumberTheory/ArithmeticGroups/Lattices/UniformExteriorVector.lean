import OAI.NumberTheory.ArithmeticGroups.Lattices.ExteriorCharacterPolynomial
import OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialCharacterDerivative
import OAI.NumberTheory.ArithmeticGroups.Lattices.UniformExteriorLine

/-! # Uniform Exterior Vector -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.UniformExteriorVector.Construction

noncomputable section

/-! For a connected semisimple group, the uniform Chevalley exterior
line is fixed pointwise. Thus the original group is the stabilizer of a
single exterior vector over every extension field. -/

open scoped Classical

theorem semisimple_polynomial_exterior_line_fixed
    {k : Type} [Field k] [CharZero k] {n r : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hconn : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    (p : Fin r → Algebraic.CoordinatePolynomial n k) (hp : LinearIndependent k p)
    (hline : ∀ (K : Type) [Field K] (ι : k →+* K) (g : G.Points ι), ∃ c : K,
      ExteriorAlgebra.ιMulti K r (fun i =>
        PolynomialAction.Construction.rightTranslate (g.val : Matrix (Fin n) (Fin n) K) (MvPolynomial.map ι (p i))) =
      c • ExteriorAlgebra.ιMulti K r (fun i => MvPolynomial.map ι (p i))) :
    ∀ (K : Type) [Field K] (ι : k →+* K) (g : G.Points ι),
      ExteriorAlgebra.ιMulti K r (fun i =>
        PolynomialAction.Construction.rightTranslate (g.val : Matrix (Fin n) (Fin n) K) (MvPolynomial.map ι (p i))) =
      ExteriorAlgebra.ιMulti K r (fun i => MvPolynomial.map ι (p i)) := by
  obtain ⟨φ, hφ⟩ := ExteriorLine.Construction.exists_dual_coordinates p hp
  have hmul := fun (K : Type) [Field K] (ι : k →+* K) =>
    ExteriorCharacterPolynomial.Construction.exteriorCharacterPolynomial_mul G p φ hφ ι (hline K ι)
  intro K _ ι g
  obtain ⟨c, hc⟩ := hline K ι g
  have he := ExteriorCharacterPolynomial.Construction.exteriorCharacterPolynomial_recovers_scalar p φ hφ ι g.val c hc
  have h1 := PolynomialCharacterDerivative.Construction.evaluate_polynomial_character_eq_one G hconn hsemi (ExteriorCharacterPolynomial.Construction.exteriorCharacterPolynomial p φ)
    (ExteriorCharacterPolynomial.Construction.exteriorCharacterPolynomial_one p φ hφ) hmul ι g
  have hc1 : c = 1 := he.symm.trans h1
  simpa only [hc1, one_smul] using hc

theorem exists_uniform_exterior_vector_stabilizer
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hconn : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple) :
    ∃ d r : ℕ, ∃ p : Fin r → Algebraic.CoordinatePolynomial n k,
      (∀ i, (p i).totalDegree ≤ d) ∧
      ∀ (K : Type) [Field K] [Algebra k K],
        LinearIndependent K (fun i => MvPolynomial.map (algebraMap k K) (p i)) ∧
        ∀ g : Algebraic.SL n K, g ∈ G.subgroup K (algebraMap k K) ↔
          ExteriorAlgebra.ιMulti K r (fun i =>
            PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) K) (MvPolynomial.map (algebraMap k K) (p i))) =
          ExteriorAlgebra.ιMulti K r (fun i => MvPolynomial.map (algebraMap k K) (p i)) := by
  obtain ⟨d, r, p, hpdeg, hline⟩ := UniformExteriorLine.Construction.exists_uniform_exterior_line_stabilizer G hconn
  have hp : LinearIndependent k p := by
    simpa only [Algebra.algebraMap_self, MvPolynomial.map_id] using (hline k).1
  have hstable : ∀ (K : Type) [Field K] (ι : k →+* K) (g : G.Points ι), ∃ c : K,
      ExteriorAlgebra.ιMulti K r (fun i =>
        PolynomialAction.Construction.rightTranslate (g.val : Matrix (Fin n) (Fin n) K) (MvPolynomial.map ι (p i))) =
      c • ExteriorAlgebra.ιMulti K r (fun i => MvPolynomial.map ι (p i)) := by
    intro K _ ι g
    let : Algebra k K := ι.toAlgebra
    obtain ⟨c, _, hc⟩ := ((hline K).2 g.val).mp g.property
    exact ⟨c, hc⟩
  have hfixed := semisimple_polynomial_exterior_line_fixed G hconn hsemi p hp hstable
  refine ⟨d, r, p, hpdeg, fun K _ _ => ⟨(hline K).1, fun g => ?_⟩⟩
  constructor
  · intro hg
    exact hfixed K (algebraMap k K) ⟨g, hg⟩
  · intro hg
    apply ((hline K).2 g).mpr
    exact ⟨1, one_ne_zero, by simpa only [one_smul] using hg⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.UniformExteriorVector.Construction
