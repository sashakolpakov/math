import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.HyperplaneCoordinates

/-! # Projective Transitions -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ProjectiveTransitions

noncomputable section

/-! The actual projective overlap units pull back to the original section ratios. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace PolarizationEmbedding

universe u
variable {S X : Scheme.{u}} {M : X.Modules} {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem openInclusion_topSection {Y : Scheme.{u}} {U V : Y.Opens} (h : V ≤ U)
    (r : Γ(Y, U)) :
    (Y.homOfLE h).appTop (U.topIso.inv r) =
      V.topIso.inv (Y.presheaf.map (homOfLE h).op r) := by
  simp only [Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv,
    ← ConcreteCategory.comp_apply, ← Y.presheaf.map_comp]
  exact ConcreteCategory.congr_hom (congrArg Y.presheaf.map (Subsingleton.elim _ _)) r

def sectionChartOnOpen (f : X ⟶ S) (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M))
    (i : Fin (n + 1)) (U : X.Opens) (hU : U ≤ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)) :
    U.toScheme ⟶ (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := Γ(S, ⊤)) i).toScheme :=
  X.homOfLE hU ≫ HyperplaneCoordinates.PolarizationEmbedding.projectiveChartOpenMap ((AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ f).appTop.hom
    (fun j => AbelianModuli.HilbertConstruction.Section.Frames.sectionRatio (s i) (s j)) i (AbelianModuli.HilbertConstruction.Section.Frames.sectionRatio_self (s i))

theorem sectionChartOnOpen_ι (f : X ⟶ S)
    (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M))
    (hs : ∀ x : X, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (i : Fin (n + 1)) (U : X.Opens) (hU : U ≤ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)) :
    sectionChartOnOpen f s i U hU ≫ (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := Γ(S, ⊤)) i).ι =
      U.ι ≫ AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs := by
  rw [sectionChartOnOpen, Category.assoc, HyperplaneCoordinates.PolarizationEmbedding.projectiveChartOpenMap_ι]
  change X.homOfLE hU ≫ AbelianModuli.HilbertConstruction.Section.ChartOverlaps.sectionAbsoluteChart f s i = _
  rw [← AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism_restrict f s hs i, ← Category.assoc, X.homOfLE_ι]

theorem sectionChartOnOpen_equation (f : X ⟶ S)
    (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M))
    (i j : Fin (n + 1)) (U : X.Opens) (hU : U ≤ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)) :
    (sectionChartOnOpen f s i U hU).appTop
      ((SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := Γ(S, ⊤)) i).topIso.inv
        (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := Γ(S, ⊤)) i j)) =
      (X.homOfLE hU).appTop (AbelianModuli.HilbertConstruction.Section.Frames.sectionRatio (s i) (s j)) := by
  rw [sectionChartOnOpen, Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply,
    HyperplaneCoordinates.PolarizationEmbedding.projectiveChartOpenMap_equation]

theorem sectionProjective_overlap_unit (f : X ⟶ S)
    (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M))
    (hs : ∀ x : X, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (i k : Fin (n + 1)) :
    let a := AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs
    let W := SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := Γ(S, ⊤)) i k
    ∃ hU : a ⁻¹ᵁ W ≤ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i),
      (a ∣_ W).appTop (W.topIso.inv
        (↑(SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := Γ(S, ⊤)) i k))) =
        (X.homOfLE hU).appTop (AbelianModuli.HilbertConstruction.Section.Frames.sectionRatio (s i) (s k)) := by
  let a := AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs
  let Y := (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).left
  let W := SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := Γ(S, ⊤)) i k
  let U := a ⁻¹ᵁ W
  have hw := SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := Γ(S, ⊤)) i k
  have hU : U ≤ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i) := (a.preimage_mono hw).trans
    (AbelianModuli.HilbertConstruction.ProjectiveChart.Preimages.sectionAbsoluteMorphism_preimage f s hs i).le
  refine ⟨hU, ?_⟩
  have hm : (a ∣_ W) ≫ Y.homOfLE hw = sectionChartOnOpen f s i U hU := by
    apply (cancel_mono (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := Γ(S, ⊤)) i).ι).mp
    rw [Category.assoc, Y.homOfLE_ι, morphismRestrict_ι,
      sectionChartOnOpen_ι f s hs]
  have hr := openInclusion_topSection hw
    (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := Γ(S, ⊤)) i k)
  change (Y.homOfLE hw).appTop
    ((SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := Γ(S, ⊤)) i).topIso.inv
      (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := Γ(S, ⊤)) i k)) =
    W.topIso.inv (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := Γ(S, ⊤)) i k) at hr
  rw [← hr, ← elementwise_of% Scheme.Hom.comp_appTop, hm]
  exact sectionChartOnOpen_equation f s i k U hU

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ProjectiveTransitions
