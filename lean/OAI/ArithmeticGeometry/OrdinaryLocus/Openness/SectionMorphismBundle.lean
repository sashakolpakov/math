import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveChartSections
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionRatioGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Preimages
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionBase

/-! # Section Morphism Bundle -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionMorphismBundle.Construction

noncomputable section

/-! The section-defined projective map pulls the coordinate bundle back to the original bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Preimages

theorem sectionMorphism_coordinateBundle_iso
    {X S : Scheme.{0}} (f : X ⟶ S) (L : X.Modules) {n : ℕ}
    (s : Fin (n + 1) → (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L))
    (hs : ∀ x : X, ∃ i, x ∈ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)) (j : Fin (n + 1)) :
    Nonempty ((Scheme.Modules.pullback (AlgebraicGeometry.AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)).obj
      (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := Γ(S, ⊤)) j).sheaf ≅ L) := by
  let P := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) Γ(S, ⊤))
  let a : X ⟶ P := AlgebraicGeometry.AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs
  let M := (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := Γ(S, ⊤)) j).sheaf
  let p := AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom (R := Γ(S, ⊤)) j
  let t (k : Fin (n + 1)) := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection a (p k)
  let U (i : Fin (n + 1)) := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)
  have ht (i : Fin (n + 1)) : U i ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (t i) := by
    have he : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (t i) = U i :=
      (AlgebraicGeometry.Quotients.FiniteDescent.SectionBase.Construction.SectionBaseChange.nonvanishing_pullback a
        (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := Γ(S, ⊤)) j) (p i)).trans
        ((congrArg (fun V : P.Opens => a ⁻¹ᵁ V)
          (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom_nonvanishing (R := Γ(S, ⊤)) j i)).trans
          (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Preimages.sectionAbsoluteMorphism_preimage f s hs i))
    exact he.symm.le
  apply SectionRatioGluing.Construction.lineBundleIso_of_local_frameCoordinates U hs t s ht
    (fun i => (le_rfl : U i ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)))
  intro i k
  have : IsIso (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (U i).ι (t i)) := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PowerLocus.pullbackSection_isIso_of_le (ht i) (t i)
  have : IsIso (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection ((U i).ι ≫ a) (p i)) :=
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Nonvanishing.isIso_pullbackSection_comp_iff a (U i).ι (p i)).mp inferInstance
  let c := ((U i).ι ≫ f).appTop.hom
  let v := fun k => AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Frames.sectionRatio (s i) (s k)
  have hvi : v i = 1 := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Frames.sectionRatio_self (s i)
  let q := ProjectiveChartFunctions.Construction.projectiveChartToOpen c v i hvi
  let V := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := Γ(S, ⊤)) i
  have he : (U i).ι ≫ a = q ≫ V.ι :=
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism_restrict f s hs i).trans (ProjectiveChartFunctions.Construction.projectiveChartToOpen_ι c v i hvi).symm
  have : IsIso (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (q ≫ V.ι) (p i)) := ProjectiveChartSections.Construction.projectiveChart_section_frame c v i hvi j
  exact (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.PullbackCoherence.frameCoordinate_pullbackComp a (U i).ι (p i) (p k)).symm.trans
    ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.PullbackCoherence.frameCoordinate_pullbackCongr he (p i) (p k)).trans
      ((ProjectiveChartSections.Construction.projectiveChart_section_coordinate c v i hvi j k).trans
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.sectionRatio_eq_frameCoordinate (s i) (s k))))

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionMorphismBundle.Construction
