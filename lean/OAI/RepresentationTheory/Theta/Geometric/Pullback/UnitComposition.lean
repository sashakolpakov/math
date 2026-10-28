import OAI.AlgebraicGeometry.SheafCohomology.Projective.PullbackFrameComposition

/-! # Unit Composition -/

namespace OAI.RepresentationTheory.Theta.Geometric.Pullback.UnitComposition

noncomputable section

/-! Canonical structure-sheaf frames respect monoidal comparisons of
composite pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

open OAI.AlgebraicGeometry.SheafCohomology.Projective.PullbackFrameComposition
universe u

local instance (X : Scheme.{u}) : MonoidalCategory X.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) : (Scheme.Modules.pullback f).Monoidal :=
  AlgebraicGeometry.SheafCohomology.Projective.PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal f

theorem pullbackUnitIso_comparison {X T U : Scheme.{u}} (f : T ⟶ X) (g : U ⟶ T) (h : U ⟶ X)
    (α : Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g ≅ Scheme.Modules.pullback h)
    [α.hom.IsMonoidal] :
    (α.app (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)).hom ≫ (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso h).hom =
      (Scheme.Modules.pullback g).map (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso f).hom ≫
        (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso g).hom := by
  let qX := AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalUnitObjIso X
  let qT := AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalUnitObjIso T
  let qU := AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalUnitObjIso U
  let ef := (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).symm
  let eg := (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).symm
  let eh := (Functor.Monoidal.εIso (Scheme.Modules.pullback h)).symm
  have hf := congrArg Iso.hom (AlgebraicGeometry.SheafCohomology.Projective.PullbackUnitMonoidal.Scheme.Modules.pullback_monoidalUnitObjIso f)
  have hg := congrArg Iso.hom (AlgebraicGeometry.SheafCohomology.Projective.PullbackUnitMonoidal.Scheme.Modules.pullback_monoidalUnitObjIso g)
  have hh := congrArg Iso.hom (AlgebraicGeometry.SheafCohomology.Projective.PullbackUnitMonoidal.Scheme.Modules.pullback_monoidalUnitObjIso h)
  change ef.hom ≫ qT.hom = (Scheme.Modules.pullback f).map qX.hom ≫
    (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso f).hom at hf
  change eg.hom ≫ qU.hom = (Scheme.Modules.pullback g).map qT.hom ≫
    (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso g).hom at hg
  change eh.hom ≫ qU.hom = (Scheme.Modules.pullback h).map qX.hom ≫
    (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso h).hom at hh
  have he := congrArg Iso.hom (AlgebraicGeometry.SheafCohomology.Projective.PullbackFrameComposition.pullbackComp_monoidalUnitIso f g h α)
  change eh.hom = (α.app (𝟙_ X.Modules)).inv ≫
    (Scheme.Modules.pullback g).map ef.hom ≫ eg.hom at he
  have he' : (α.app (𝟙_ X.Modules)).hom ≫ eh.hom =
      (Scheme.Modules.pullback g).map ef.hom ≫ eg.hom := by
    rw [he]
    simp
  apply (cancel_epi ((Scheme.Modules.pullback g).map ((Scheme.Modules.pullback f).map qX.hom))).1
  simp only [← Category.assoc]
  have hn := α.hom.naturality qX.hom
  change (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback f).map qX.hom) ≫
    (α.app (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)).hom =
    (α.app (𝟙_ X.Modules)).hom ≫ (Scheme.Modules.pullback h).map qX.hom at hn
  rw [hn]
  simp only [Category.assoc]
  rw [← hh]
  simp only [← Category.assoc]
  rw [he']
  simp only [Category.assoc]
  rw [hg]
  rw [← Category.assoc, ← Functor.map_comp, hf, Functor.map_comp]
  simp only [Category.assoc]

end

end OAI.RepresentationTheory.Theta.Geometric.Pullback.UnitComposition
