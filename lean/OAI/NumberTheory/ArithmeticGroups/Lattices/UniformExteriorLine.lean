import OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialBasisExtension
import OAI.NumberTheory.ArithmeticGroups.Lattices.UniformPolynomialStabilizer
import OAI.NumberTheory.ArithmeticGroups.Lattices.ExteriorLine

/-! # Uniform Exterior Line -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.UniformExteriorLine.Construction

noncomputable section

/-! A single exterior-line construction over the original field detects
the matrix group over all extension fields. -/

open scoped Classical TensorProduct
open _root_.MvPolynomial Set

theorem exists_uniform_exterior_line_stabilizer
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) :
    ∃ d r : ℕ, ∃ p : Fin r → Algebraic.CoordinatePolynomial n k,
      (∀ i, (p i).totalDegree ≤ d) ∧
      ∀ (K : Type) [Field K] [Algebra k K],
        LinearIndependent K (fun i => MvPolynomial.map (algebraMap k K) (p i)) ∧
        ∀ g : Algebraic.SL n K, g ∈ G.subgroup K (algebraMap k K) ↔
          ∃ c : K, c ≠ 0 ∧
            ExteriorAlgebra.ιMulti K r (fun i =>
              PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) K)
                (MvPolynomial.map (algebraMap k K) (p i))) =
              c • ExteriorAlgebra.ιMulti K r (fun i => MvPolynomial.map (algebraMap k K) (p i)) := by
  obtain ⟨d, hd⟩ := UniformPolynomialStabilizer.Construction.exists_uniform_polynomial_subspace_stabilizer G hG
  let W := PolynomialStabilizer.Construction.boundedVanishingSpace G d
  let : Module.Finite k W := Module.Finite.of_fg (PolynomialStabilizer.Construction.boundedVanishingSpace_fg G d)
  let r := Module.finrank k W
  let b : Module.Basis (Fin r) k W := Module.finBasis k W
  let p : Fin r → Algebraic.CoordinatePolynomial n k := fun i => (b i).val
  refine ⟨d, r, p, fun i => ?_, fun K _ _ => ?_⟩
  · exact (mem_restrictTotalDegree _ _ _).mp (b i).property.2
  · obtain ⟨hlin, hspan⟩ := PolynomialBasisExtension.Construction.polynomial_basis_extension (K := K) W b
    refine ⟨hlin, fun g => ?_⟩
    let q : Fin r → Algebraic.CoordinatePolynomial n K := fun i => MvPolynomial.map (algebraMap k K) (p i)
    have htrans : LinearIndependent K
        (fun i => PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) K) (q i)) :=
      hlin.map' (PolynomialAction.Construction.rightTranslateEquiv g).toLinearMap
        (LinearMap.ker_eq_bot.mpr (PolynomialAction.Construction.rightTranslateEquiv g).injective)
    have hspanR : Submodule.span K (range (fun i =>
        PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) K) (q i))) =
        (Submodule.span K (range q)).map
          (PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) K)).toLinearMap := by
      rw [Submodule.map_span, ← range_comp]
      rfl
    have hline := ExteriorLine.Construction.span_eq_iff_exterior_smul (show LinearIndependent K q from hlin) htrans
    rw [hspanR, hspan] at hline
    exact (hd K g).trans hline

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.UniformExteriorLine.Construction
