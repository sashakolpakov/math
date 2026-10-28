import OAI.NumberTheory.Quaternion.Arithmetic.AdelicLatticeMahler
import OAI.NumberTheory.Quaternion.Arithmetic.CompactIntegralValues
import OAI.NumberTheory.Quaternion.Arithmetic.AdelicNormValues

/-! # Finite Norm Values -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.FiniteNormValues

noncomputable section

/-! Short vectors in quaternion adelic lattices may be chosen with
reduced norm in one finite set of nonzero rational values. -/

open scoped Classical _root_.NumberField _root_.Quaternion
open _root_.NumberField _root_.NumberField.mixedEmbedding Set QuaternionAlgebra

variable {F : Type} [Field F] [NumberField F]

theorem quaternion_nonsplit_finite_short_norm_values (a b : F) (ha : a ≠ 0)
    (hs : ¬ ∃ x y : F, x ^ 2 - a * y ^ 2 = b) :
    ∃ C : Set (Fin 4 → mixedSpace F), IsCompact C ∧ ∃ T : Set F, T.Finite ∧
      (∀ c ∈ T, c ≠ 0) ∧
      ∀ (g : FiniteAdelicMatrices.FiniteAdelicGroupPoints (MatrixGroup.quaternionNormOneMatrixGroup a b))
        (h : (MatrixGroup.quaternionNormOneMatrixGroup a b).ArchimedeanProduct Set.univ),
        ∃ x ∈ FiniteAdelicLattice.finiteAdelicMatrixLattice (FiniteAdelicMatrices.finiteAdelicMatrix (MatrixGroup.quaternionNormOneMatrixGroup a b) g),
          Norm.quaternionNorm a b (MatrixGroup.quaternionOfCoordinates a b x) ∈ T ∧
          ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F 4
            (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv (MatrixGroup.quaternionNormOneMatrixGroup a b) h).val
              (fun i => mixedEmbedding F (x i)) ∈ C := by
  obtain ⟨C, hC, hvectors⟩ := AdelicLatticeMahler.quaternion_nonsplit_compact_adelic_vectors a b ha hs
  obtain ⟨d, hd, hnorm⟩ := AdelicNormValues.quaternion_finiteAdelic_lattice_norm_integral a b
  have hdF : (d : F) ≠ 0 := by exact_mod_cast hd
  let P := MinkowskiLocalProjections.mixedPolynomialValue (MatrixGroup.quaternionNormPolynomial a b)
  let T : Set F := {c | (d : F) * c ∈ (algebraMap (𝓞 F) F).range ∧
    mixedEmbedding F c ∈ P '' C ∧ c ≠ 0}
  have hT : T.Finite :=
    (CompactIntegralValues.finite_rational_values_in_compact (d : F) hdF (P '' C)
      (hC.image (MinkowskiLocalProjections.continuous_mixedPolynomialValue _))).subset (fun _ h => ⟨h.1, h.2.1⟩)
  refine ⟨C, hC, T, hT, fun _ hc => hc.2.2, ?_⟩
  intro g h
  obtain ⟨x, hx, hx0, harch⟩ := hvectors g h
  refine ⟨x, hx, ⟨hnorm g x hx, ?_, ?_⟩, harch⟩
  · refine ⟨_, harch, ?_⟩
    dsimp only [P]
    rw [MinkowskiLocalProjections.mixedPolynomialValue_archimedean_invariant (MatrixGroup.quaternionNormOneMatrixGroup a b)
      (MatrixGroup.quaternionNormPolynomial a b)
      (fun v g y => MatrixGroup.quaternionMatrixPoint_preserves_normPolynomial (algebraMap F v.Completion) a b g y),
      MinkowskiLocalProjections.mixedPolynomialValue_diagonal]
    apply congrArg (mixedEmbedding F)
    exact MatrixGroup.quaternionNormPolynomial_eval (RingHom.id F) a b x
  · intro hz
    have hq := SplitCriterion.quaternion_norm_anisotropic_of_no_splitting_equation a b ha hs
      (MatrixGroup.quaternionOfCoordinates a b x) hz
    apply hx0
    apply (linearEquivTuple a 0 b).symm.injective
    exact hq.trans (map_zero (linearEquivTuple a 0 b).symm).symm

end

end OAI.NumberTheory.Quaternion.Arithmetic.FiniteNormValues
