import OAI.AlgebraicGeometry.FormalGeometry.Completion.RigidificationScalarNaturality

/-! # Composed Section Associativity -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ComposedSectionAssociativity

noncomputable section

/-! Iterating the geometric pullback of a section agrees with the
single composite pullback, including its coefficient comparison. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

namespace Construction

universe u

theorem pullbackComposedSection_assoc {X Y Z W : Scheme.{u}}
    (f : Y ⟶ X) (j : Z ⟶ Y) (k : W ⟶ Z) (M : X.Modules)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ (Scheme.Modules.pullback f).obj M) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection k (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j s ≫ (Scheme.Modules.pullbackComp j f).hom.app M) ≫
      (Scheme.Modules.pullbackComp k (j ≫ f)).hom.app M =
    (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (k ≫ j) s ≫ (Scheme.Modules.pullbackComp (k ≫ j) f).hom.app M) ≫
      (Scheme.Modules.pullbackCongr (Category.assoc k j f)).hom.app M := by
  rw [PullbackStructureComparison.Construction.pullbackSection_targetMap, Category.assoc, PullbackEqualityComparisons.Construction.pullbackComp_three_forward k j f M]
  rw [reassoc_of% (PullbackSectionComposition.Construction.pullbackSection_comp j k ((Scheme.Modules.pullback f).obj M) s)]
  exact (Category.assoc _ _ _).symm

theorem frameAxisScalar_congr_top {X Y S T : Scheme.{u}}
    (f f' : Y ⟶ X) (hf : f = f') (b : T ⟶ Y) (g : T ⟶ S) (s : S ⟶ X)
    (h : b ≫ f = g ≫ s) (h' : b ≫ f' = g ≫ s) (M : X.Modules)
    (r : (Scheme.Modules.pullback s).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj M) :
    Rigidified.FrameScalar.Construction.frameAxisScalar f' b g s h' M r (e ≪≫ (Scheme.Modules.pullbackCongr hf).app M) =
      Rigidified.FrameScalar.Construction.frameAxisScalar f b g s h M r e := by
  subst f'
  have he : e ≪≫ (Scheme.Modules.pullbackCongr (rfl : f = f)).app M = e := by
    apply Iso.ext
    change e.hom ≫ 𝟙 _ = e.hom
    exact Category.comp_id _
  exact congrArg (Rigidified.FrameScalar.Construction.frameAxisScalar f b g s h M r) he

theorem frameAxisScalar_congr_base {X Y S T : Scheme.{u}}
    (f : Y ⟶ X) (b : T ⟶ Y) (g g' : T ⟶ S) (hg : g = g') (s : S ⟶ X)
    (h : b ≫ f = g ≫ s) (h' : b ≫ f = g' ≫ s) (M : X.Modules)
    (r : (Scheme.Modules.pullback s).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj M) :
    Rigidified.FrameScalar.Construction.frameAxisScalar f b g' s h' M r e = Rigidified.FrameScalar.Construction.frameAxisScalar f b g s h M r e := by
  subst g'
  rfl

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ComposedSectionAssociativity
