import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionMorphismBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.ProjectivePresentation
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectivePresentation

/-! # Ample Embedding Power -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AmpleEmbeddingPower.Construction

noncomputable section

/-! An ample bundle has a positive power identified with the coordinate bundle of a closed embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem ample_exists_closed_embedding_power
    {X S : Scheme.{0}} [IsAffine S] (f : X ⟶ S) [IsProper f]
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hL : L.IsAmple) :
    ∃ (d : ℕ), 0 < d ∧ ∃ (n : ℕ)
      (a : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) Γ(S, ⊤))),
      IsClosedImmersion a ∧
      a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := Γ(S, ⊤)) (σ := Fin (n + 1)) = f ≫ S.toSpecΓ ∧
      Nonempty ((Scheme.Modules.pullback a).obj
        (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := Γ(S, ⊤)) (0 : Fin (n + 1))).sheaf ≅
          (L.tensorPower d).sheaf) := by
  have : CompactSpace X := ⟨hL.1⟩
  have : X.IsSeparated := ⟨by rw [← CategoryTheory.Limits.terminal.comp_from f]; infer_instance⟩
  obtain ⟨d, hd, k, s, hs, ha⟩ := hL.projective_section_family
  obtain ⟨e, he, n, q, j, hq, hgen⟩ := (L.tensorPower d).generating_power_family f s ha
  have hD (i : Fin (k + 1)) : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (q (j i)) = AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i) :=
    (congrArg AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (hq i)).trans (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PowerLocus.sectionNonvanishing_tensorPowerSection (s i) e he)
  have hcover (x : X) : ∃ i, x ∈ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (q (j i)) := by
    obtain ⟨i, hi⟩ := hs x
    exact ⟨i, (hD i).symm ▸ hi⟩
  have hqcover (x : X) : ∃ i, x ∈ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (q i) := by
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨j i, hi⟩
  have hqa (i : Fin (k + 1)) : IsAffineOpen (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (q (j i))) :=
    (hD i).symm ▸ ha i
  let a : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) Γ(S, ⊤)) :=
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f q hqcover
  have hc : IsClosedImmersion a :=
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.SelectedSectionEmbedding.sectionAbsoluteMorphism_closedImmersion_of_selected f q hqcover j hcover hqa hgen
  obtain ⟨eb⟩ := SectionMorphismBundle.Construction.sectionMorphism_coordinateBundle_iso f _ q hqcover 0
  refine ⟨e * d, Nat.mul_pos he hd, n, a, hc, ?_, ?_⟩
  · rw [← AlgebraicGeometry.Quotients.FiniteDescent.ProjectivePresentation.Construction.ProjectivePresentationEmbedding.base_eq]
    exact AlgebraicGeometry.AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism_over f q hqcover
  · exact ⟨eb ≪≫ (L.tensorPowerComposeIso e d).symm⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AmpleEmbeddingPower.Construction
