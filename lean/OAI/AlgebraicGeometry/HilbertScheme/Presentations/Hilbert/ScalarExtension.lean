import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ScalarExtension

/-! # Scalar Extension -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ScalarExtension.GradedHilbert

noncomputable section

/-!
Initial ideals and Hilbert functions commute with extending a coefficient
field. A linear functional detecting a leading coefficient supplies the
reverse inclusion of initial monomial ideals.
-/

open _root_.MvPolynomial _root_.Module

universe u v

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L] {n : ℕ}

theorem degree_map_field (m : MonomialOrder (Fin (n + 1))) (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) :
    m.degree (MvPolynomial.map (algebraMap K L) f) = m.degree f := by
  unfold MonomialOrder.degree
  rw [support_map_of_injective f (algebraMap K L).injective]

theorem degree_coefficientApply (m : MonomialOrder (Fin (n + 1)))
    (φ : L →ₗ[K] K) (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing L n) (hφ : φ (f.coeff (m.degree f)) ≠ 0) :
    CoefficientMaps.GradedHilbert.coefficientApply φ f ≠ 0 ∧ m.degree (CoefficientMaps.GradedHilbert.coefficientApply φ f) = m.degree f := by
  have hs : m.degree f ∈ (CoefficientMaps.GradedHilbert.coefficientApply φ f).support := mem_support_iff.mpr hφ
  refine ⟨?_, m.toSyn.injective ?_⟩
  · intro hzero
    simp only [hzero, support_zero, Finset.notMem_empty] at hs
  · apply le_antisymm
    · apply m.degree_le_iff.mpr
      intro a ha
      exact m.le_degree (CoefficientMaps.GradedHilbert.support_coefficientApply_subset φ f ha)
    · exact m.le_degree hs

def initialExponentSet (m : MonomialOrder (Fin (n + 1)))
    (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) : Set (Fin (n + 1) →₀ ℕ) :=
  m.degree '' {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n | f ∈ I ∧ f ≠ 0}

theorem initialIdeal_scalarExtended (m : MonomialOrder (Fin (n + 1)))
    (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) :
    InitialIdeal.GradedHilbert.initialIdeal m (CoefficientMaps.GradedHilbert.scalarExtendedIdeal (L := L) I) =
      (MonomialBasis.GradedHilbert.monomialSpan L (initialExponentSet m I)).toIdeal := by
  have hmono (a : Fin (n + 1) →₀ ℕ) :
      monomial a (1 : L) ∈ InitialIdeal.GradedHilbert.initialIdeal m (CoefficientMaps.GradedHilbert.scalarExtendedIdeal (L := L) I) ↔
        monomial a (1 : L) ∈ (MonomialBasis.GradedHilbert.monomialSpan L (initialExponentSet m I)).toIdeal := by
    rw [InitialIdeal.GradedHilbert.monomial_mem_initialIdeal_iff, Uniform.MonomialBound.GradedHilbert.monomial_mem_monomialSpan_iff]
    constructor
    · rintro ⟨f, hf, hf0, hfa⟩
      obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero K
        (m.coeff_degree_ne_zero_iff.mpr hf0)
      obtain ⟨hq0, hdeg⟩ := degree_coefficientApply m φ f hφ
      refine ⟨m.degree (CoefficientMaps.GradedHilbert.coefficientApply φ f), ?_, ?_⟩
      · exact ⟨CoefficientMaps.GradedHilbert.coefficientApply φ f, ⟨CoefficientMaps.GradedHilbert.coefficientApply_mem_of_mem_scalarExtendedIdeal I φ hf, hq0⟩,
          rfl⟩
      · rw [hdeg]
        exact hfa
    · rintro ⟨a', ⟨f, ⟨hf, hf0⟩, rfl⟩, hfa⟩
      refine ⟨MvPolynomial.map (algebraMap K L) f,
        Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap K L)) hf, ?_, ?_⟩
      · intro hzero
        apply hf0
        exact (MvPolynomial.map_injective _ (algebraMap K L).injective)
          (hzero.trans (map_zero (MvPolynomial.map (algebraMap K L))).symm)
      · rw [degree_map_field]
        exact hfa
  have hLeft := InitialIdeal.GradedHilbert.initialIdeal_isMonomial m (CoefficientMaps.GradedHilbert.scalarExtendedIdeal (L := L) I)
  have hRight : SaturatedMonomialIdeals.GradedHilbert.IsMonomial (MonomialBasis.GradedHilbert.monomialSpan L (initialExponentSet m I)).toIdeal := ⟨_, rfl⟩
  apply Ideal.ext
  intro f
  rw [hLeft.mem_iff_support, hRight.mem_iff_support]
  simp only [hmono]

theorem hilbertFunction_scalarExtended (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (d : ℕ) :
    Hilbert.Polynomial.GradedHilbert.hilbertFunction (CoefficientMaps.GradedHilbert.scalarExtendedIdeal (L := L) I.toIdeal) d = Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal d := by
  let m : MonomialOrder (Fin (n + 1)) := MonomialOrder.lex
  let J := ScalarExtension.GradedHilbert.scalarExtendedHomogeneousIdeal (L := L) I
  calc
    Hilbert.Polynomial.GradedHilbert.hilbertFunction (CoefficientMaps.GradedHilbert.scalarExtendedIdeal (L := L) I.toIdeal) d =
        Hilbert.Polynomial.GradedHilbert.hilbertFunction (InitialIdeal.GradedHilbert.initialIdeal m J.toIdeal) d := (InitialIdeal.GradedHilbert.hilbertFunction_initialIdeal m J d).symm
    _ = Hilbert.Polynomial.GradedHilbert.hilbertFunction (MonomialBasis.GradedHilbert.monomialSpan L (initialExponentSet m I.toIdeal)).toIdeal d := by
      exact congrArg (fun J => Hilbert.Polynomial.GradedHilbert.hilbertFunction J d) (initialIdeal_scalarExtended m I.toIdeal)
    _ = Hilbert.Polynomial.GradedHilbert.hilbertFunction (MonomialBasis.GradedHilbert.monomialSpan K (initialExponentSet m I.toIdeal)).toIdeal d :=
      (MonomialBasis.GradedHilbert.hilbertFunction_monomialSpan_field_independent (K := K) L _ d).symm
    _ = Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal d := InitialIdeal.GradedHilbert.hilbertFunction_initialIdeal m I d

theorem hasHilbertPolynomial_scalarExtended_iff (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n))
    (P : Polynomial ℚ) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (CoefficientMaps.GradedHilbert.scalarExtendedIdeal (L := L) I.toIdeal) P ↔
      Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P := by
  simp only [Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial, hilbertFunction_scalarExtended]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ScalarExtension.GradedHilbert
