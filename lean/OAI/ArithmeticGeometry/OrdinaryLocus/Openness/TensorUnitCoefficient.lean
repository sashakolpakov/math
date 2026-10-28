import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorSectionRestriction
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PositivePowerChartGenerator
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Gluing

/-! # Tensor Unit Coefficient -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnitCoefficient.Construction

noncomputable section

/-! Tensor normalization by a unit section agrees with ordinary frame coefficients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective.PositivePowerChartGenerator OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Gluing

universe u

local instance tensorUnitCoefficientMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

theorem sectionHom_pullback_isIso_of_overCoefficient_one
    {X : Scheme.{u}} {P : X.Modules} (s : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ P) (U : X.Opens)
    (e : P.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (hs : AlgebraicGeometry.SheafCohomology.Projective.FrameSections.overTrivializationCoefficient P U e (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv P s) = 1) :
    IsIso ((Scheme.Modules.pullback U.ι).map s) := by
  have hc : e.hom.val.app (.op (Over.mk (𝟙 U))) (s.app U (1 : Γ(X, U))) = (1 : Γ(X, U)) := by
    exact (congrArg (e.hom.val.app (.op (Over.mk (𝟙 U))))
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Gluing.moduleSectionHomEquiv_restrict P s U)).symm.trans hs
  have he := AlgebraicGeometry.Quotients.FiniteDescent.OverSection.Construction.OverSectionLocus.coordinate_eq s U e 1 hc
  have hi : IsIso (s.over U ≫ e.hom) := by
    rw [he]
    exact (AlgebraicGeometry.Quotients.FiniteDescent.OverSection.Construction.OverSectionLocus.scalar_isIso_iff U 1).mpr isUnit_one
  have : IsIso (s.over U) := (isIso_comp_right_iff _ e.hom).mp hi
  exact (TensorSectionFrame.Construction.moduleMap_over_isIso_iff s U).mp this

theorem moduleIso_inv_hom_app {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (U : X.Opens) (x : Γ(N, U)) : e.hom.app U (e.inv.app U x) = x := by
  have h := congrArg (fun q : N ⟶ N => q.val.app (.op U)) e.inv_hom_id
  exact ConcreteCategory.congr_hom h x

theorem tensorSectionGlobalCoefficient_unit_apply
    {X : Scheme.{u}} {P : X.Modules} (a : 𝟙_ X.Modules ⟶ P) (U : X.Opens)
    [IsIso ((Scheme.Modules.pullback U.ι).map a)] (x : Γ(P, ⊤)) :
    a.app U (TensorSectionRestriction.Construction.tensorSectionGlobalCoefficient (𝟙_ X.Modules) a U ((λ_ P).inv.app ⊤ x)) =
      P.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op x := by
  let z := TensorSectionRestriction.Construction.tensorSectionGlobalCoefficient (𝟙_ X.Modules) a U ((λ_ P).inv.app ⊤ x)
  have ht : (TensorSectionFrame.Construction.tensorByUnitSection (𝟙_ X.Modules) a).app U z =
      (𝟙_ X.Modules ⊗ P).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        ((λ_ P).inv.app ⊤ x) :=
    (TensorSectionFrame.Construction.tensorSectionFrameAppEquiv (𝟙_ X.Modules) a U).apply_symm_apply _
  have hu := congrArg (fun q : 𝟙_ X.Modules ⟶ P => q.app U z)
    (TensorSectionFrame.Construction.tensorByUnitSection_unit a)
  change (λ_ P).hom.app U ((TensorSectionFrame.Construction.tensorByUnitSection (𝟙_ X.Modules) a).app U z) = a.app U z at hu
  rw [ht] at hu
  have hn := PresheafOfModules.naturality_apply (λ_ P).hom.val
    (homOfLE (le_top : U ≤ ⊤)).op ((λ_ P).inv.app ⊤ x)
  have he : (λ_ P).hom.app ⊤ ((λ_ P).inv.app ⊤ x) = x := by
    exact moduleIso_inv_hom_app (λ_ P) ⊤ x
  change (λ_ P).hom.app U
      ((𝟙_ X.Modules ⊗ P).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        ((λ_ P).inv.app ⊤ x)) =
      P.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        ((λ_ P).hom.app ⊤ ((λ_ P).inv.app ⊤ x)) at hn
  exact hu.symm.trans (hn.trans (congrArg (P.presheaf.map (homOfLE le_top).op) he))

theorem tensorSectionGlobalCoefficient_unit_frame
    {X : Scheme.{u}} {P : X.Modules} (s : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ P) (U : X.Opens)
    (e : P.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (hs : AlgebraicGeometry.SheafCohomology.Projective.FrameSections.overTrivializationCoefficient P U e (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv P s) = 1)
    [IsIso ((Scheme.Modules.pullback U.ι).map ((AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalUnitObjIso X).hom ≫ s))]
    (x : Γ(P, ⊤)) :
    (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalUnitObjIso X).hom.app U
      (TensorSectionRestriction.Construction.tensorSectionGlobalCoefficient (𝟙_ X.Modules) ((AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalUnitObjIso X).hom ≫ s) U
        ((λ_ P).inv.app ⊤ x)) = AlgebraicGeometry.SheafCohomology.Projective.FrameSections.overTrivializationCoefficient P U e x := by
  have : IsIso ((Scheme.Modules.pullback U.ι).map s) :=
    sectionHom_pullback_isIso_of_overCoefficient_one s U e hs
  have : IsIso (s.app U) := TensorSectionFrame.Construction.moduleMap_app_isIso_of_pullback s U
  apply (ConcreteCategory.bijective_of_isIso (s.app U)).injective
  have h := tensorSectionGlobalCoefficient_unit_apply ((AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalUnitObjIso X).hom ≫ s) U x
  change s.app U ((AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalUnitObjIso X).hom.app U _) = _ at h
  refine h.trans ?_
  rw [AlgebraicGeometry.SheafCohomology.Projective.PositivePowerChartGenerator.restrict_eq_coefficient_smul_generator P U e (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv P s) x hs]
  have hr := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Gluing.moduleSectionHomEquiv_restrict P s U
  have ht := congrArg (fun y : Γ(P, U) => AlgebraicGeometry.SheafCohomology.Projective.FrameSections.overTrivializationCoefficient P U e x • y) hr
  have hl := s.app_smul (AlgebraicGeometry.SheafCohomology.Projective.FrameSections.overTrivializationCoefficient P U e x) (1 : Γ(X, U))
  change s.app U (show Γ(X, U) from AlgebraicGeometry.SheafCohomology.Projective.FrameSections.overTrivializationCoefficient P U e x * 1) =
    AlgebraicGeometry.SheafCohomology.Projective.FrameSections.overTrivializationCoefficient P U e x • s.app U (1 : Γ(X, U)) at hl
  rw [mul_one] at hl
  exact ht.trans hl.symm

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnitCoefficient.Construction
