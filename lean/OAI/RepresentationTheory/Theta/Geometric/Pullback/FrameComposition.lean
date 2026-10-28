import OAI.RepresentationTheory.Theta.Geometric.Pullback.UnitComposition

/-! # Frame Composition -/

namespace OAI.RepresentationTheory.Theta.Geometric.Pullback.FrameComposition

noncomputable section

/-! Native frames respect the canonical composition of module pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

universe u

local instance (X : Scheme.{u}) : MonoidalCategory X.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) : (Scheme.Modules.pullback f).Monoidal :=
  AlgebraicGeometry.SheafCohomology.Projective.PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal f

theorem pullbackUnitIso_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.pullbackComp f g).app (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Z) ≪≫
      AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso (f ≫ g) =
    (Scheme.Modules.pullback f).mapIso (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso g) ≪≫
      AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso f := by
  let : (Scheme.Modules.pullbackComp f g).hom.IsMonoidal :=
    AlgebraicGeometry.SheafCohomology.Projective.PullbackCompMonoidal.Scheme.Modules.pullbackComp_hom_isMonoidal f g
  apply Iso.ext
  exact UnitComposition.pullbackUnitIso_comparison g f (f ≫ g) (Scheme.Modules.pullbackComp f g)

def pullbackGlobalFrame {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    (e : M ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y) :
    (Scheme.Modules.pullback f).obj M ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X :=
  (Scheme.Modules.pullback f).mapIso e ≪≫ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso f

theorem pullbackGlobalFrame_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (e : M ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Z) :
    (Scheme.Modules.pullbackComp f g).app M ≪≫ pullbackGlobalFrame (f ≫ g) e =
      pullbackGlobalFrame f (pullbackGlobalFrame g e) := by
  apply Iso.ext
  have hn := (Scheme.Modules.pullbackComp f g).hom.naturality e.hom
  change (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map e.hom) ≫
    ((Scheme.Modules.pullbackComp f g).app (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Z)).hom =
    ((Scheme.Modules.pullbackComp f g).app M).hom ≫ (Scheme.Modules.pullback (f ≫ g)).map e.hom at hn
  have hu := congrArg Iso.hom (pullbackUnitIso_comp f g)
  simp only [Iso.trans_hom, Functor.mapIso_hom] at hu
  simp only [pullbackGlobalFrame, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← Category.assoc, ← hn, Category.assoc, hu]

end

end OAI.RepresentationTheory.Theta.Geometric.Pullback.FrameComposition
