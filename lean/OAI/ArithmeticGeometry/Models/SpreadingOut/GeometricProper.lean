import OAI.ArithmeticGeometry.Models.SpreadingOut.GoodOpenFiber
import OAI.ArithmeticGeometry.Models.SpreadingOut.FiniteTypeCoefficientBase
import OAI.ArithmeticGeometry.Models.SpreadingOut.DedekindGeometric
import OAI.ArithmeticGeometry.Models.SpreadingOut.DedekindCoefficient

/-! # Geometric Proper -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.GeometricProper.Construction

noncomputable section

/-! Smooth proper geometrically irreducible schemes over a number field
admit smooth proper models with geometrically irreducible fibers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u

theorem open_stage_has_geometric_proper_coefficient_model
    {K : Type u} [Field K] [NumberField K] {W X : Over (Spec (.of K))}
    {f : W ⟶ X} {s : Finset K} (L : OpenImmersionStages.Constructions.Foundations.OpenImmersionAtBase s f)
    [IsIntegral X.left] [Smooth L.target.hom] [IsProper L.target.hom]
    [GeometricallyIrreducible L.source.hom] :
    ∃ N : Foundations.Constructions.CoefficientModel K X,
      Smooth N.model.hom ∧ IsProper N.model.hom ∧ GeometricallyIrreducible N.model.hom := by
  obtain ⟨D⟩ := DedekindCoefficient.Construction.coefficient_has_dedekind_base (K := K) s
  let R := D.carrier
  let b := D.baseMap
  let g := Spec.map (CommRingCat.ofHom D.genericMap.toRingHom)
  have hgb : g ≫ b = CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s := D.generic_comp
  let F := Over.pullback b
  let M : Over (Spec (.of R)) := F.obj L.target
  let V : Over (Spec (.of R)) := F.obj L.source
  let i : V ⟶ M := F.map L.inclusion
  have : IsOpenImmersion L.inclusion.left := L.openInclusion
  have : IsOpenImmersion i.left := MorphismProperty.of_isPullback
    (FoundationsPullback.Constructions.pullback_over_map_isPullback b L.inclusion).flip inferInstance
  have : Smooth M.hom := inferInstanceAs (Smooth (pullback.snd L.target.hom b))
  have : IsProper M.hom := inferInstanceAs (IsProper (pullback.snd L.target.hom b))
  have : GeometricallyIrreducible V.hom :=
    inferInstanceAs (GeometricallyIrreducible (pullback.snd L.source.hom b))
  let eL : (Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).obj L.target ≅ X :=
    Over.isoMk L.targetCartesian.isoPullback.symm L.targetCartesian.isoPullback_inv_snd
  let eM : (Over.pullback g).obj M ≅ X :=
    BaseChange.Constructions.Foundations.iteratedBaseChangeIso b g L.target ≪≫ Scheme.Constructions.Foundations.baseChangeCongr hgb L.target ≪≫ eL
  have : IsIso eM.inv.left := inferInstanceAs (IsIso ((Over.forget (Spec (.of K))).map eM.inv))
  have : IsIntegral ((Over.pullback g).obj M).left := IsIntegral.of_isIso eM.inv.left
  have : IsIntegral M.left := SmoothGeometricIntegrality.Construction.smooth_model_integral_of_integral_generic
    D.genericMap.toRingHom D.injective M
  exact DedekindGeometric.Construction.dedekind_good_open_has_geometric_coefficient_model R D.genericMap
    D.injective i X eM

theorem smooth_proper_geometricallyIrreducible_has_coefficient_model
    {K : Type u} [Field K] [NumberField K]
    (X : Over (Spec (.of K))) [Smooth X.hom] [IsProper X.hom]
    [GeometricallyIrreducible X.hom] :
    ∃ N : Foundations.Constructions.CoefficientModel K X,
      Smooth N.model.hom ∧ IsProper N.model.hom ∧ GeometricallyIrreducible N.model.hom := by
  obtain ⟨W, f, MW, hWaff, hf, _, _, hMW⟩ :=
    GoodOpen.Construction.smooth_geometricallyIrreducible_has_good_open_model K X
  have : IsAffine W.left := hWaff
  have : IsOpenImmersion f.left := hf
  have : GeometricallyIrreducible MW.model.hom := hMW
  have : GeometricallyConnected MW.model.hom := by
    refine ⟨fun k _ y Z p q hp ↦ ?_⟩
    have : IrreducibleSpace Z := GeometricallyIrreducible.geometrically_irreducibleSpace y p q hp
    infer_instance
  obtain ⟨MX, hs, hp⟩ := Finite.Construction.smooth_proper_has_coefficient_model X
  have : Smooth MX.model.hom := hs
  have : IsProper MX.model.hom := hp
  obtain ⟨s, L, _, hirr, hsL, hpL⟩ := OpenModel.Construction.open_immersion_models_with_geometry f MW MX
  have : GeometricallyIrreducible L.source.hom := hirr
  have : Smooth L.target.hom := hsL
  have : IsProper L.target.hom := hpL
  have : IrreducibleSpace X.left := self_of_isIntegral_of_geometrically
    (f := X.hom) GeometricallyIrreducible.geometrically_irreducibleSpace
  have : IsReduced X.left := SmoothComponents.Construction.smooth_scheme_reduced X.hom
  have : IsIntegral X.left := isIntegral_of_irreducibleSpace_of_isReduced X.left
  exact open_stage_has_geometric_proper_coefficient_model L

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.GeometricProper.Construction
