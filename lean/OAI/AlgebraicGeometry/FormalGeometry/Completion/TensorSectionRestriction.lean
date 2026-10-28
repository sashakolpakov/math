import OAI.AlgebraicGeometry.FormalGeometry.Completion.TensorSectionMap

/-! # Tensor Section Restriction -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.TensorSectionRestriction

noncomputable section

/-! Tensoring by a section commutes with restriction to an open subscheme. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory MonoidalCategory

namespace Construction

universe u

attribute [local instance] SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory

theorem restrict_structureLeftUnitor_inv {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (M : X.Modules) :
    (Scheme.Modules.restrictFunctor f).map (TensorSectionMap.Construction.structureLeftUnitor M).inv ≫
      (SheafCohomology.Projective.TensorSections.restrictMonoidalTensorIso f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) M).hom =
    (TensorSectionMap.Construction.structureLeftUnitor (M.restrict f)).inv ≫
      ((Scheme.Modules.restrictUnitIso f).inv ⊗ₘ 𝟙 (M.restrict f)) := by
  let F := Scheme.Modules.restrictFunctor f
  let : (Scheme.Modules.pullback f).Monoidal := SheafCohomology.Projective.PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal f
  let : F.Monoidal := Functor.Monoidal.transport (Scheme.Modules.restrictFunctorIsoPullback f).symm
  have hu := SheafCohomology.Projective.TensorFrameSections.poleTensor_restrict_monoidalUnitObjIso f
  change F.map (SheafCohomology.Projective.TensorSections.monoidalUnitObjIso X).hom ≫ (Scheme.Modules.restrictUnitIso f).hom =
    Functor.OplaxMonoidal.η F ≫ (SheafCohomology.Projective.TensorSections.monoidalUnitObjIso Y).hom at hu
  have hc : Functor.LaxMonoidal.ε F ≫ F.map (SheafCohomology.Projective.TensorSections.monoidalUnitObjIso X).hom =
      (SheafCohomology.Projective.TensorSections.monoidalUnitObjIso Y).hom ≫ (Scheme.Modules.restrictUnitIso f).inv := by
    apply (cancel_mono (Scheme.Modules.restrictUnitIso f).hom).mp
    rw [Category.assoc, hu]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact Functor.Monoidal.ε_η_assoc F (SheafCohomology.Projective.TensorSections.monoidalUnitObjIso Y).hom
  change F.map ((λ_ M).inv ≫ ((SheafCohomology.Projective.TensorSections.monoidalUnitObjIso X).hom ⊗ₘ 𝟙 M)) ≫
      Functor.OplaxMonoidal.δ F (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) M = _
  rw [F.map_comp, Category.assoc]
  erw [← Functor.OplaxMonoidal.δ_natural]
  rw [Functor.Monoidal.map_leftUnitor_inv]
  simp only [F.map_id, Category.assoc, Functor.Monoidal.μ_δ_assoc]
  rw [← tensorHom_id]
  erw [tensorHom_comp_tensorHom]
  rw [Category.id_comp, hc]
  change (λ_ (F.obj M)).inv ≫
      (((SheafCohomology.Projective.TensorSections.monoidalUnitObjIso Y).hom ≫ (Scheme.Modules.restrictUnitIso f).inv) ⊗ₘ 𝟙 (F.obj M)) = _
  simp only [TensorSectionMap.Construction.structureLeftUnitor, Iso.trans_inv, tensorIso_inv, Iso.symm_inv,
    Iso.refl_inv, Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
  rfl

theorem restrict_tensorSectionMap {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] {P : X.Modules}
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ P) (M : X.Modules) :
    (Scheme.Modules.restrictFunctor f).map (TensorSectionMap.Construction.tensorSectionMap s M) ≫
      (SheafCohomology.Projective.TensorSections.restrictMonoidalTensorIso f P M).hom =
    TensorSectionMap.Construction.tensorSectionMap ((Scheme.Modules.restrictUnitIso f).inv ≫
      (Scheme.Modules.restrictFunctor f).map s) (M.restrict f) := by
  let F := Scheme.Modules.restrictFunctor f
  let : (Scheme.Modules.pullback f).Monoidal := SheafCohomology.Projective.PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal f
  let : F.Monoidal := Functor.Monoidal.transport (Scheme.Modules.restrictFunctorIsoPullback f).symm
  change F.map ((TensorSectionMap.Construction.structureLeftUnitor M).inv ≫ (s ⊗ₘ 𝟙 M)) ≫
      Functor.OplaxMonoidal.δ F P M = _
  rw [F.map_comp, Category.assoc, ← Functor.OplaxMonoidal.δ_natural]
  rw [← Category.assoc]
  have hu := restrict_structureLeftUnitor_inv f M
  change F.map (TensorSectionMap.Construction.structureLeftUnitor M).inv ≫
    Functor.OplaxMonoidal.δ F (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) M = _ at hu
  rw [hu]
  simp only [F.map_id, TensorSectionMap.Construction.tensorSectionMap, Category.assoc,
    tensorHom_comp_tensorHom, Category.id_comp]
  rfl

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.TensorSectionRestriction
