import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.EdgeHomologyNaturality

/-! # Derived Comparison Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.DerivedComparisonNaturality.IntrinsicCech

noncomputable section

/-! The acyclic-cover comparison with derived global sections is natural in the coefficient sheaf in every positive degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
universe u
variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)
local instance : (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive

theorem cechPositiveRightDerivedIso_naturality
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : F ⟶ G) (hU : ⨆ i, U i = ⊤)
    (hF : AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic U F) (hG : AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic U G) (n : ℕ) :
    HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) (n + 1) ≫
        (IntrinsicCech.SheafCohomologyComparison.cechPositiveRightDerivedIso U G hU hG n).hom =
      (IntrinsicCech.SheafCohomologyComparison.cechPositiveRightDerivedIso U F hU hF n).hom ≫
        ((TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).rightDerived (n + 1)).map f := by
  let IF := injectiveResolution F
  let IG := injectiveResolution G
  let phi : InjectiveResolution.Hom IF IG f :=
    { hom := InjectiveResolution.desc f IG IF
      ι_f_zero_comp_hom_f_zero := InjectiveResolution.desc_commutes_zero f IG IF }
  let c := HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) (n + 1)
  let s := HomologicalComplex.homologyMap (ResolutionSections.IntrinsicCech.cechResolutionSectionsMap phi.hom) (n + 1)
  let t := HomologicalComplex.homologyMap (InjectiveVerticalEdge.IntrinsicCech.cechInjectiveResolutionTotalMap U phi.hom) (n + 1)
  let v₁ := IntrinsicCech.SheafCohomologyComparison.cechPositiveVerticalHomologyIso U F hF n
  let v₂ := IntrinsicCech.SheafCohomologyComparison.cechPositiveVerticalHomologyIso U G hG n
  let w₁ := IntrinsicCech.SheafCohomologyComparison.cechPositiveHorizontalHomologyIso U F hU n
  let w₂ := IntrinsicCech.SheafCohomologyComparison.cechPositiveHorizontalHomologyIso U G hU n
  let d₁ := IF.isoRightDerivedObj (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X) (n + 1)
  let d₂ := IG.isoRightDerivedObj (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X) (n + 1)
  let r := ((TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).rightDerived (n + 1)).map f
  have hv : c ≫ v₂.hom = v₁.hom ≫ t :=
    EdgeHomologyNaturality.IntrinsicCech.cechPositiveVerticalHomologyIso_naturality U f phi hF hG n
  have hw : s ≫ w₂.hom = w₁.hom ≫ t :=
    EdgeHomologyNaturality.IntrinsicCech.cechPositiveHorizontalHomologyIso_naturality U f phi hU n
  have hi : t ≫ w₂.inv = w₁.inv ≫ s :=
    EdgeHomologyNaturality.IntrinsicCech.isoSquare_inv_naturality w₁ w₂ s t hw
  have hd : s ≫ d₂.inv = d₁.inv ≫ r := EdgeHomologyNaturality.IntrinsicCech.cechResolutionDerived_naturality f phi n
  change c ≫ (v₂.hom ≫ w₂.inv ≫ d₂.inv) = (v₁.hom ≫ w₁.inv ≫ d₁.inv) ≫ r
  calc
    _ = (c ≫ v₂.hom) ≫ (w₂.inv ≫ d₂.inv) := (Category.assoc _ _ _).symm
    _ = (v₁.hom ≫ t) ≫ (w₂.inv ≫ d₂.inv) :=
      congrArg (fun z => z ≫ (w₂.inv ≫ d₂.inv)) hv
    _ = v₁.hom ≫ ((t ≫ w₂.inv) ≫ d₂.inv) :=
      (Category.assoc v₁.hom t (w₂.inv ≫ d₂.inv)).trans
        (congrArg (fun z => v₁.hom ≫ z) (Category.assoc t w₂.inv d₂.inv).symm)
    _ = v₁.hom ≫ ((w₁.inv ≫ s) ≫ d₂.inv) :=
      congrArg (fun z => v₁.hom ≫ (z ≫ d₂.inv)) hi
    _ = v₁.hom ≫ w₁.inv ≫ (s ≫ d₂.inv) :=
      congrArg (fun z => v₁.hom ≫ z) (Category.assoc w₁.inv s d₂.inv)
    _ = v₁.hom ≫ w₁.inv ≫ (d₁.inv ≫ r) :=
      congrArg (fun z => v₁.hom ≫ w₁.inv ≫ z) hd
    _ = _ :=
      (congrArg (fun z => v₁.hom ≫ z) (Category.assoc w₁.inv d₁.inv r).symm).trans
        (Category.assoc v₁.hom (w₁.inv ≫ d₁.inv) r).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.DerivedComparisonNaturality.IntrinsicCech
