import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.PullbackValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.CoordinatePullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.SectionPullbackComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ComponentRatios

/-! # Projective Coordinate Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveCoordinatePullback

noncomputable section

/-! The projective morphism supplied by generating sections pulls each ambient coordinate function back to the actual ratio of those sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {X S : Scheme.{u}} {M : X.Modules} {n : ℕ} (f : X ⟶ S)
variable (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ M))
variable (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))

theorem sectionAbsoluteMorphism_coordinate_on_frame (i j : Fin (n + 1))
    (h : Ample.LineBundles.sectionNonvanishing (s i) ≤ SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs ⁻¹ᵁ
      Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n) (MvPolynomial.X i)) :
    Open.SectionPullback.openSectionPullback (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)
      (Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n) (MvPolynomial.X i)) (Ample.LineBundles.sectionNonvanishing (s i)) h
      (Quotient.CoordinatePullback.projectiveCoordinateFunction Γ(S, ⊤) i j) =
      ComponentRatios.sectionComponentRatio (s i) (s j) (Ample.LineBundles.sectionNonvanishing (s i)) le_rfl := by
  let U := Ample.LineBundles.sectionNonvanishing (s i)
  let P := Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n) (MvPolynomial.X i)
  let r := Quotient.CoordinatePullback.projectiveCoordinateFunction Γ(S, ⊤) i j
  have hm : ⊤ ≤ (U.ι ≫ SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) ⁻¹ᵁ P := by
    intro x _
    exact h x.property
  have hc : ⊤ ≤ ChartOverlaps.sectionAbsoluteChart f s i ⁻¹ᵁ P := by
    dsimp [P]
    rw [ProjectiveChart.Preimages.sectionAbsoluteChart_preimage, Scheme.Opens.ι_preimage_self]
  have he := Open.SectionPullbackComposition.openSectionPullback_comp U.ι (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) P U ⊤
    h U.ι_preimage_self.ge hm r
  have hg := Open.SectionPullbackComposition.openSectionPullback_congr (SectionsProjectiveMorphism.sectionAbsoluteMorphism_restrict f s hs i)
    P ⊤ hm hc r
  have hv : Open.SectionPullback.openSectionPullback (ChartOverlaps.sectionAbsoluteChart f s i) P ⊤ hc r = Frames.sectionRatio (s i) (s j) :=
    ProjectiveChart.PullbackValues.projectiveChartMap_coordinate_pullback ((Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ f).appTop.hom
      (fun k => Frames.sectionRatio (s i) (s k)) i (Frames.sectionRatio_self (s i)) hc j
  have ha := (Open.SectionPullbackComposition.openSectionPullback_open_self U
    (Open.SectionPullback.openSectionPullback (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) P U h r)).symm.trans
      (he.trans (hg.trans hv))
  have hb := (congrArg U.topIso.inv (ComponentRatios.sectionRatio_component (s i) (s j)).symm).trans
    (ConcreteCategory.congr_hom U.topIso.hom_inv_id (Frames.sectionRatio (s i) (s j)))
  exact (ConcreteCategory.bijective_of_isIso U.topIso.inv).1 (ha.trans hb.symm)

theorem sectionAbsoluteMorphism_coordinate_pullback (i j : Fin (n + 1))
    (V : X.Opens) (hV : V ≤ Ample.LineBundles.sectionNonvanishing (s i))
    (h : V ≤ SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs ⁻¹ᵁ
      Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n) (MvPolynomial.X i)) :
    Open.SectionPullback.openSectionPullback (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)
      (Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n) (MvPolynomial.X i)) V h
      (Quotient.CoordinatePullback.projectiveCoordinateFunction Γ(S, ⊤) i j) = ComponentRatios.sectionComponentRatio (s i) (s j) V hV := by
  have hi := (ProjectiveChart.Preimages.sectionAbsoluteMorphism_preimage f s hs i).ge
  have he := Open.SectionPullback.openSectionPullback_restrict_target (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)
    (Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n) (MvPolynomial.X i)) (Ample.LineBundles.sectionNonvanishing (s i)) V hi hV
    (Quotient.CoordinatePullback.projectiveCoordinateFunction Γ(S, ⊤) i j)
  exact he.symm.trans ((congrArg (X.presheaf.map (homOfLE hV).op)
    (sectionAbsoluteMorphism_coordinate_on_frame f s hs i j hi)).trans
      (ComponentRatios.sectionComponentRatio_restrict (s i) (s j) (Ample.LineBundles.sectionNonvanishing (s i)) V hV le_rfl))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveCoordinatePullback
