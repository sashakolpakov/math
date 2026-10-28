import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismPresentationsGraphs
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismPairCutdown

/-! # Automorphism Stratum -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismStratum

noncomputable section

/-! On a fixed source-polynomial stratum, the constructed polarized
automorphism parameter classifies every reduced test scheme, without
noetherian or field hypotheses on the test. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem exists_bounded_polarized_automorphism_stratum
    {S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.abelian.scheme.left) (d : ℕ)
    (hP : AbelianModuli.HilbertConstruction.Tensor.Powers.IsTensorPower (Relative.PoincareSimilitude.RelativePoincareClasses.polarizationLine A.dual
      A.polarization.isogeny.hom).sheaf d P.sheaf)
    {n : ℕ} (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left ⟶ P.sheaf))
    (hs : ∀ x : A.abelian.scheme.left, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (he : IsClosedImmersion (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom s hs).left)
    (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0}) (Q : Polynomial ℚ) :
    ∃ Z : Over S, IsReduced Z.left ∧ IsNoetherian Z.left ∧
      LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ IsSeparated Z.hom ∧
      ∃ u : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback Z.hom) (A.pullback Z.hom),
        ∀ (T : Over S) [IsReduced T.left]
          (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (A.pullback T.hom)),
          (∀ t : T.left, AutomorphismSourcePolynomial.polarizedAutomorphismGraphPolynomial
            (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he) (T.hom t) = Q) →
          ∃ f : T ⟶ Z, EndomorphismFamiliesId.EndomorphismFamilies.restrict A.abelian f (Finite.Actions.GroupEndRing.ofHom _ u.abelian.hom) =
            Finite.Actions.GroupEndRing.ofHom _ e.abelian.hom := by
  let BA := SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he
  obtain ⟨B, M, hB, hft, hqc, hsep, r, hM⟩ :=
    Presentations.BoundedEndomorphismTuples.exists_e34_bounded_endomorphism_tuples A.abelian hPresentations BA (n := 2) (fun _ => Q)
  have : LocallyOfFiniteType M.hom := hft
  have : QuasiCompact M.hom := hqc
  have : IsSeparated M.hom := hsep
  have : IsLocallyNoetherian M.left := LocallyOfFiniteType.isLocallyNoetherian M.hom
  have : CompactSpace M.left := QuasiCompact.compactSpace_of_compactSpace M.hom
  have : IsNoetherian M.left := ⟨⟩
  obtain ⟨Z, j, hr, hj, u, hu, hZ⟩ :=
    AutomorphismPairCutdown.exists_reduced_polarized_automorphism_pair_cutdown A M (r 0) (r 1)
  have : IsClosedImmersion j.left := hj
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian j.left
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace j.left
  have : IsNoetherian Z.left := ⟨⟩
  have hZft : LocallyOfFiniteType Z.hom := by rw [← j.w]; infer_instance
  have hZqc : QuasiCompact Z.hom := by rw [← j.w]; infer_instance
  have hZsep : IsSeparated Z.hom := by rw [← j.w]; infer_instance
  refine ⟨Z, hr, inferInstance, hZft, hZqc, hZsep, u, ?_⟩
  intro T _ e hT
  have hg := AutomorphismPresentationsGraphs.polarized_automorphism_inverse_pair_e34_graphs A P d hP s hs he B hB Q T hT e
  obtain ⟨f, hf, _⟩ := (hM T ![Finite.Actions.GroupEndRing.ofHom _ e.abelian.hom,
    Finite.Actions.GroupEndRing.ofHom _ e.abelian.inv]).mp hg
  obtain ⟨k, hk, _⟩ := hZ T f e (hf 0) (hf 1)
  refine ⟨k, ?_⟩
  exact (congrArg (EndomorphismFamiliesId.EndomorphismFamilies.restrict A.abelian k) hu).trans
    ((EndomorphismFamiliesId.EndomorphismFamilies.restrict_comp A.abelian k j (r 0)).symm.trans
      ((congrArg (fun f => EndomorphismFamiliesId.EndomorphismFamilies.restrict A.abelian f (r 0)) hk).trans (hf 0)))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismStratum
