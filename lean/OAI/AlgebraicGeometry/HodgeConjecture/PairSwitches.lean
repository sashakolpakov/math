import OAI.AlgebraicGeometry.HodgeConjecture.Coordinates
import OAI.Geometry.ComplexTorus.RiemannProjectivity.Realization

/-! # Pair Switches -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.PairSwitches

noncomputable section

/-!
# Unconditional PairSwitches, with the manuscript's coordinate and H¹ interfaces

The historical theorem has exactly its committed type and now composes the
proved RiemannProjectivity realization theorem. The native strengthening below also records
one-coordinate transpositions and the realized embedding signs in actual H¹.
The original statement and conditional proof are preserved in their files.
-/

open scoped BigOperators

namespace CM

/-- PairSwitches: balanced lists are connected by pair switches through
odd CM types, with every intermediate type admitting realization. -/
theorem connectivity_by_pair_switches
    (E : IntermediateField ℚ ℂ)
    [NumberField E]
    [IsGalois ℚ E]
    [NumberField.IsCMField E]
    (p : ℕ)
    (v w : Fin p →
      ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
        (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (hbalance : ∀ τ : Gal(E/ℚ),
      (∑ i : Fin p, ComplexMultiplication.SignSwitch.CM.signValue ((v i).val τ)) =
        ∑ i : Fin p, ComplexMultiplication.SignSwitch.CM.signValue ((w i).val τ)) :
    ∃ (n : ℕ)
      (path : Fin (n + 1) → Fin p →
        ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
          (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)),
      path 0 = v ∧
      path (Fin.last n) = w ∧
      (∀ k : Fin n,
        ComplexMultiplication.OddSignSwitch.CM.OddFourFactorSwitch (path k.castSucc) (path k.succ)) ∧
      (∀ (k : Fin (n + 1)) (i : Fin p),
        Nonempty
          (ComplexMultiplication.CMKnownResults.CM.HodgeRealization
            (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (path k i)))) := by
  exact Coordinates.PairSwitches.connectivity_by_pair_switches E
    (Geometry.ComplexTorus.RiemannProjectivity.Realization.CM.realization_of_cm_sign_type E) p v w hbalance

end CM

open OAI.AlgebraicGeometry.HodgeConjecture.PairSwitches.CM

/-- The realized embedding vectors have precisely the prescribed native H¹ types. -/
theorem realized_embedding_types
    (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E]
    [NumberField.IsCMField E]
    (u : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
      (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E u)) :
    (∀ τ : Gal(E/ℚ),
      R.comparison.toLinearMap.baseChange ℂ
          (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ)) ∈
        R.abelianVariety.h1Holomorphic ↔ u.val τ = true) ∧
    (∀ τ : Gal(E/ℚ),
      R.comparison.toLinearMap.baseChange ℂ
          (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ)) ∈
        R.abelianVariety.h1Antiholomorphic ↔ u.val τ = false) := by
  constructor
  · intro τ
    exact (R.holomorphic _).trans (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure_holomorphic E u τ)
  · intro τ
    exact (R.antiholomorphic _).trans (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure_antiholomorphic E u τ)

/-- PairSwitches with each representative-coordinate transposition and each actual
H¹ embedding type explicit. No realization or compatibility premise remains. -/
theorem connectivity_by_coordinate_transpositions
    (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E]
    [NumberField.IsCMField E]
    (p : ℕ)
    (v w : Fin p → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
      (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (hbalance : ∀ τ : Gal(E/ℚ),
      (∑ i : Fin p, ComplexMultiplication.SignSwitch.CM.signValue ((v i).val τ)) =
        ∑ i : Fin p, ComplexMultiplication.SignSwitch.CM.signValue ((w i).val τ)) :
    ∃ (n : ℕ)
      (path : Fin (n + 1) → Fin p → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
        (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)),
      path 0 = v ∧ path (Fin.last n) = w ∧
      (∀ k : Fin n, Coordinates.PairSwitches.OddCoordinateTransposition (path k.castSucc) (path k.succ)) ∧
      (∀ k : Fin n, ComplexMultiplication.OddSignSwitch.CM.OddFourFactorSwitch (path k.castSucc) (path k.succ)) ∧
      (∀ (k : Fin (n + 1)) (i : Fin p),
        ∃ R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (path k i)),
          (∀ τ : Gal(E/ℚ),
            R.comparison.toLinearMap.baseChange ℂ
                (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E
                  (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ)) ∈
              R.abelianVariety.h1Holomorphic ↔ (path k i).val τ = true) ∧
          (∀ τ : Gal(E/ℚ),
            R.comparison.toLinearMap.baseChange ℂ
                (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E
                  (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ)) ∈
              R.abelianVariety.h1Antiholomorphic ↔ (path k i).val τ = false)) := by
  classical
  let : LinearOrder Gal(E/ℚ) := linearOrderOfSTO WellOrderingRel
  let : Fintype Gal(E/ℚ) := Fintype.ofFinite _
  obtain ⟨n, path, hzero, hlast, hcoordinate, hfour⟩ :=
    Coordinates.PairSwitches.coordinate_path_of_signSum_eq
      (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)
      (ComplexMultiplication.ExteriorSignReduction.CM.CMCoefficientField.conjugation_mul_involutive E)
      (ComplexMultiplication.ExteriorSignReduction.CM.CMCoefficientField.conjugation_mul_ne E) v w hbalance
  refine ⟨n, path, hzero, hlast, hcoordinate, hfour, ?_⟩
  intro k i
  obtain ⟨R⟩ := Geometry.ComplexTorus.RiemannProjectivity.Realization.CM.realization_of_cm_sign_type E (path k i).val (path k i).property
  exact ⟨R, realized_embedding_types E (path k i) R⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.PairSwitches
