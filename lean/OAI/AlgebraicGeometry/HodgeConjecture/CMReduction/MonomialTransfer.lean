import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CanonicalTuple
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.BasisNormalization
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.LineTransfer

/-! # Monomial Transfer -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.MonomialTransfer.CM.Construction

noncomputable section

/-! Transfer a realized endpoint construction to each actual exterior
embedding monomial, using multilinearity and algebraic H1 pullback spans. -/

open _root_.CategoryTheory
open scoped TensorProduct Classical

variable {A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1)}
local instance (D : ComplexMultiplication.Decomposition.CM.CMDecomposition H) : LinearOrder D.EmbeddingIndex := linearOrderOfSTO WellOrderingRel

theorem monomial_algebraic_of_endpoint
    (D : ComplexMultiplication.Decomposition.CM.CMDecomposition H) (C : ComplexMultiplication.KnownExteriorCohomology.CM.AbelianExteriorComparison A H)
    (hhol : H.holomorphic = A.h1Holomorphic) (hanti : H.antiholomorphic = A.h1Antiholomorphic)
    (hrealization : ComplexMultiplication.CMKnownResults.CM.KnownResults.RiemannH1Realization D.commonCoefficientField)
    (hfullness : ComplexMultiplication.KnownAlgebraicity.CM.KnownResults.RationalH1MapsAreAlgebraic)
    (p : ℕ) (s : D.ExteriorIndex (p + p))
    (hendpoint : Endpoints.CM.Construction.EndpointAlgebraicity D.commonCoefficientField p
      (fun i => D.galoisOddSign (D.exteriorEmbeddingTuple (p + p) s (Fin.castAdd p i)))
      (fun i => (D.galoisOddSign (D.exteriorEmbeddingTuple (p + p) s (Fin.natAdd p i))).neg)) :
    C.complexMap (p + p) (D.complexExteriorEmbeddingBasis (p + p) s) ∈
      A.variety.complexGeometricAlgebraicClasses p := by
  let j := D.exteriorEmbeddingTuple (p + p) s
  let v := fun i => D.galoisOddSign (j i)
  let R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (D.embeddingLineSource (j i)) := fun i =>
    Classical.choice (hrealization (D.embeddingLineSource (j i))
      ⟨ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure_polarization D.commonCoefficientField (v i)⟩)
  let B : Fin (p + p) → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety := fun i => (R i).abelianVariety
  let τ := ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv D.commonCoefficientField 1
  let u : ∀ i, ComplexMultiplication.WeightOne.CM.Complexification ((B i).variety.rationalCohomology 1) := fun i =>
    (R i).comparison.toLinearMap.baseChange ℂ ((D.embeddingLineSource_cm (j i)).embeddingBasis τ)
  let f : ∀ i, ComplexMultiplication.WeightOne.CM.Complexification ((B i).variety.rationalCohomology 1) →ₗ[ℂ]
      ComplexMultiplication.WeightOne.CM.Complexification (A.variety.rationalCohomology 1) := fun i =>
    (D.embeddingLineTransfer (j i)).comp ((R i).comparison.symm.toLinearMap.baseChange ℂ)
  have hf (i : Fin (p + p)) : f i ∈ (B i).algebraicH1PullbackSpan A :=
    LineTransfer.CM.Construction.realized_lineTransfer_mem hfullness D hhol hanti (j i) (R i)
  have hgeom : ∀ (g : ∀ i, A.toOver ⟶ (B i).toOver), (∀ i, IsMonHom (g i)) →
      IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace A.toOver) (p + p)
        (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (g i)
          (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace (B i).toOver) 1 (u i))) ∈
        A.variety.complexGeometricAlgebraicClasses p := by
    intro g _
    have hc := CanonicalTuple.CM.Construction.canonical_tuple_of_endpoint D.commonCoefficientField p v hendpoint R A g
    have hb := BasisNormalization.CM.Construction.h1Cup_basis_of_canonical D.commonCoefficientField p
      (fun i => D.embeddingLineSource (j i)) (fun i => D.embeddingLineSource_cm (j i)) R A g
      (fun _ => τ) hc
    convert hb using 3
    rfl
  have ht := MultilinearTransfer.CM.Construction.h1Cup_algebraic_of_pullback_spans A p B u hgeom f hf
  have hu (i : Fin (p + p)) : f i (u i) = D.embeddingBasis (j i) := by
    have hi := LineTransfer.CM.Construction.realized_lineTransfer_basis D (j i) (R i)
    convert hi using 3
  simp only [hu] at ht
  rw [IteratedCup.CM.Construction.complexMap_embeddingMonomial C D (p + p) s]
  convert ht using 3

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.MonomialTransfer.CM.Construction
