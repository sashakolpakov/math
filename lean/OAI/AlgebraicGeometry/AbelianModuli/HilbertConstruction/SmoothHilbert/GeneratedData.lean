import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmoothHilbert.FamilyDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GeneratedReconstruction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GenerationBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.IdealBaseChange

/-! # Generated Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Smooth Hilbert families over arbitrary rings have finite generated quotient data with the prescribed uniform bounds. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Flat.ClosedFamilies.FlatClosedHilbertFamily.exists_generatedData
    {R : Type u} [CommRing R] {n : ℕ} {P : Polynomial ℚ}
    (F : Flat.ClosedFamilies.FlatClosedHilbertFamily R n P) [Smooth F.val.scheme.hom]
    (N : ℕ) (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N) (B : ℕ) (hB : N ≤ B) :
    ∃ D : {D : Truncated.GradedClassification.TruncatedGradedQuotientData R (Fin (n + 1)) B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) //
      D.GeneratedFromDegree N}, D.val.projectiveIdeal = F.val.ideal := by
  obtain ⟨K, _, hK, G, _, hF⟩ := F.exists_smooth_noetherian_hilbert_family
  have : IsNoetherianRing K := hK
  let I := G.saturatedIdeal
  let D₀ := I.generatedData N hN B
  have hD₀ : D₀.val.projectiveIdeal = G.val.ideal :=
    (Uniform.GeneratedReconstruction.uniformGeneratedTruncation_projectiveIdeal I.ideal I.saturated P I.hilbert N hN B hB).trans
      (HilbertScheme.Presentations.Projective.IdealEquivalence.GradedHilbert.projectiveQuotient_homogeneousIdealOfSheaf G.val.ideal)
  let φ : CommRingCat.of K ⟶ CommRingCat.of R := CommRingCat.ofHom K.val.toRingHom
  refine ⟨⟨D₀.val.baseChange R,
    D₀.val.generatedFromDegree_baseChange (R := .of K) (A := .of R) N D₀.property⟩, ?_⟩
  calc
    (D₀.val.baseChange R).projectiveIdeal = D₀.val.projectiveIdeal.comap (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n) :=
      D₀.val.projectiveIdeal_baseChange (A := R)
    _ = G.val.ideal.comap (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n) :=
      congrArg (fun J : (Projective.ProjectivePresentations.affineProjectiveSpace K n).left.IdealSheafData => J.comap (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n)) hD₀
    _ = F.val.ideal := congrArg Closed.Families.FlatClosedFamily.ideal hF.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
