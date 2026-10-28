import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar
import OAI.AlgebraicGeometry.FormalGeometry.Completion.PullbackSquarePasting
import OAI.AlgebraicGeometry.FormalGeometry.Completion.PullbackStructureComparison

/-! # Rigidification Comparison Pasting -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.RigidificationComparisonPasting

noncomputable section

/-! The reference trivialization along a rigidified axis is compatible
with a further base change of the family. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

namespace Construction

universe u

@[reassoc]
theorem rigidificationBaseChangeIso_hom {X Y S T : Scheme.{u}}
    (f : Y ⟶ X) (b : T ⟶ Y) (g : T ⟶ S) (s : S ⟶ X) (h : b ≫ f = g ≫ s)
    (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S) :
    (Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b g s h M r).hom =
      (Quotients.FiniteDescent.PullbackSectionCongr.Construction.PullbackSectionSquare.iso f s b g h M).hom ≫
        (Scheme.Modules.pullback g).map r.hom ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g).hom := by
  simp only [Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso, Quotients.FiniteDescent.PullbackSectionCongr.Construction.PullbackSectionSquare.iso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]

@[reassoc]
theorem rigidificationBaseChangeIso_paste {X Y Z S T U : Scheme.{u}}
    (f : Y ⟶ X) (j : Z ⟶ Y) (s : S ⟶ X) (b : T ⟶ Y) (g : T ⟶ S)
    (c : U ⟶ Z) (t : U ⟶ T) (h : c ≫ j = t ≫ b) (h₀ : b ≫ f = g ≫ s)
    (h₁ : c ≫ (j ≫ f) = (t ≫ g) ≫ s) (M : X.Modules)
    (r : (Scheme.Modules.pullback s).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S) :
    (Scheme.Modules.pullback c).map ((Scheme.Modules.pullbackComp j f).hom.app M) ≫
      (Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso (j ≫ f) c (t ≫ g) s h₁ M r).hom =
    (Quotients.FiniteDescent.PullbackSectionCongr.Construction.PullbackSectionSquare.iso j b c t h ((Scheme.Modules.pullback f).obj M)).hom ≫
      (Scheme.Modules.pullback t).map (Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b g s h₀ M r).hom ≫
        (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso t).hom := by
  simp only [rigidificationBaseChangeIso_hom, Functor.map_comp, Category.assoc]
  rw [PullbackSquarePasting.Construction.pullbackSquare_paste_assoc f j s b g c t h h₀ h₁ M]
  have hn := (Scheme.Modules.pullbackComp t g).hom.naturality r.hom
  change (Scheme.Modules.pullback t).map ((Scheme.Modules.pullback g).map r.hom) ≫
      (Scheme.Modules.pullbackComp t g).hom.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S) =
    (Scheme.Modules.pullbackComp t g).hom.app ((Scheme.Modules.pullback s).obj M) ≫
      (Scheme.Modules.pullback (t ≫ g)).map r.hom at hn
  rw [← reassoc_of% hn, PullbackStructureComparison.Construction.structureModulePullbackIso_comp t g]

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.RigidificationComparisonPasting
