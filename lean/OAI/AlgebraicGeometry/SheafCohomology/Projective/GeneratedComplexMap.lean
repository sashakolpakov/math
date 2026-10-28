import OAI.AlgebraicGeometry.SheafCohomology.Projective.AmpleComplexEmbedding
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteGlobalGenerators

/-! # Generated Complex Map -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GeneratedComplexMap

noncomputable section

/-! A globally generated line bundle is the genuine hyperplane pullback
of a morphism to native complex projective space. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem generated_exists_complex_projective_map {X : Scheme}
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (hL : FiniteGlobalGenerators.HasFiniteGlobalGenerators L.sheaf) :
    ∃ (n : ℕ) (a : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n),
      a ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n = f ∧
      Nonempty ((Scheme.Modules.pullback a).obj
        (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := ℂ) (0 : Fin (n + 1))).sheaf ≅ L.sheaf) := by
  classical
  obtain ⟨I, hI, s, hs⟩ := hL.section_cover L
  let := hI
  let n := Fintype.card I
  let q : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf) :=
    Fin.lastCases 0 (fun k => s ((Fintype.equivFin I).symm k))
  have hq : ∀ x : X, ∃ k, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (q k) := by
    intro x
    obtain ⟨k, hk⟩ := hs x
    refine ⟨((Fintype.equivFin I) k).castSucc, ?_⟩
    simpa only [q, Fin.lastCases_castSucc, Equiv.symm_apply_apply] using hk
  let a := AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f q hq
  have hb : a ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤)) = f ≫ Foundations.Scheme.ProjectiveSpace.complexBase.toSpecΓ := by
    rw [← Quotients.FiniteDescent.ProjectivePresentation.Construction.ProjectivePresentationEmbedding.base_eq]
    exact AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism_over f q hq
  obtain ⟨eL⟩ := ArithmeticGeometry.OrdinaryLocus.Openness.SectionMorphismBundle.Construction.sectionMorphism_coordinateBundle_iso f L.sheaf q hq 0
  let R := Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤)
  let e : ℂ ≃+* R := (Scheme.ΓSpecIso (.of ℂ)).symm.commRingCatIsoToRingEquiv
  let π := ScalarBundle.projectiveScalarIso e n
  have hbase : Foundations.Scheme.ProjectiveSpace.complexBase.toSpecΓ ≫ Spec.map (CommRingCat.ofHom e.toRingHom) = 𝟙 Foundations.Scheme.ProjectiveSpace.complexBase := by
    have he : Spec.map (CommRingCat.ofHom e.toRingHom) = Foundations.Scheme.ProjectiveSpace.complexBase.isoSpec.inv :=
      (Scheme.isoSpec_Spec_inv (.of ℂ)).symm
    rw [he]
    exact Foundations.Scheme.ProjectiveSpace.complexBase.isoSpec.hom_inv_id
  have hπ : π.hom ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) =
      MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) ≫ Spec.map (CommRingCat.ofHom e.toRingHom) :=
    ScalarBundle.projectiveScalarMap_over e.toRingHom n
  refine ⟨n, a ≫ π.hom, ?_, ⟨?_⟩⟩
  · rw [ComplexBase.projectiveSpaceToBase_eq_homogeneousProjπ, Category.assoc,
      hπ, ← Category.assoc, hb, Category.assoc, hbase, Category.comp_id]
  · exact (Scheme.Modules.pullbackComp a π.hom).symm.app _ ≪≫
      (Scheme.Modules.pullback a).mapIso (ScalarBundle.projectiveScalarMap_bundleIso e.toRingHom n 0 0) ≪≫ eL

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GeneratedComplexMap
