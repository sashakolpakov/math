import OAI.AlgebraicGeometry.Foundations.Scheme.ClosedProjective
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Open Ambient -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.OpenAmbient.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: the scheme-theoretic graph factorization

These are the actual graph, fiber product, and projection of a complex
scheme morphism. The source structure morphism is written `f.left ≫ Y.structureMap`,
which equals `X.structureMap` by the defining equation of a morphism over ℂ.

This file constructs the geometry preceding the refined Gysin map. It does
not assert that a closed immersion alone supplies such a map on Chow groups.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}

/-- The fiber product containing the graph, with the source base map
written as the composite supplied by the morphism over the base. -/
def graphAmbient (f : X.toOver ⟶ Y.toOver) : Scheme :=
  pullback (f.left ≫ Y.structureMap) Y.structureMap

/-- The first projection of the graph's ambient product. -/
def graphFirstProjection (f : X.toOver ⟶ Y.toOver) : graphAmbient f ⟶ X.carrier :=
  pullback.fst (f.left ≫ Y.structureMap) Y.structureMap

/-- The projection along which flat pullback is used in the graph construction. -/
def graphSecondProjection (f : X.toOver ⟶ Y.toOver) : graphAmbient f ⟶ Y.carrier :=
  pullback.snd (f.left ≫ Y.structureMap) Y.structureMap

/-- The actual scheme-theoretic graph morphism. -/
def graph (f : X.toOver ⟶ Y.toOver) : X.carrier ⟶ graphAmbient f :=
  pullback.lift (𝟙 X.carrier) f.left (Category.id_comp (f.left ≫ Y.structureMap))

@[simp]
theorem graph_firstProjection (f : X.toOver ⟶ Y.toOver) :
    graph f ≫ graphFirstProjection f = 𝟙 X.carrier :=
  pullback.lift_fst _ _ _

@[simp]
theorem graph_secondProjection (f : X.toOver ⟶ Y.toOver) :
    graph f ≫ graphSecondProjection f = f.left :=
  pullback.lift_snd _ _ _

/-- The graph is a closed immersion because the target is separated over ℂ. -/
instance graph_isClosedImmersion (f : X.toOver ⟶ Y.toOver) :
    IsClosedImmersion (graph f) := by
  have hsep : IsSeparated Y.structureMap :=
    @IsProper.toIsSeparated _ _ _ Y.projective.isProper
  exact @IsSeparated.instIsClosedImmersionLiftSchemeId X.carrier Y.carrier Foundations.Scheme.ProjectiveSpace.complexBase
    f.left Y.structureMap hsep

/-- The first projection is the base change of the smooth target structure map. -/
instance graphFirstProjection_smooth (f : X.toOver ⟶ Y.toOver) :
    Smooth (graphFirstProjection f) := by
  exact AlgebraicGeometry.instSmoothFstScheme (f.left ≫ Y.structureMap) Y.structureMap

/-- The second projection is the base change of the smooth source structure map. -/
instance graphSecondProjection_smooth (f : X.toOver ⟶ Y.toOver) :
    Smooth (graphSecondProjection f) := by
  have hbase : f.left ≫ Y.structureMap = X.structureMap := f.w
  have : Smooth (f.left ≫ Y.structureMap) := hbase.symm ▸ X.smooth
  exact AlgebraicGeometry.instSmoothSndScheme (f.left ≫ Y.structureMap) Y.structureMap

instance graphSecondProjection_flat (f : X.toOver ⟶ Y.toOver) :
    Flat (graphSecondProjection f) := by infer_instance

end

/-! Actual open maps of source and target induce the corresponding open map of graph ambient products. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {X Y X' Y' : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (g : X'.toOver ⟶ Y'.toOver)
    (a : X'.toOver ⟶ X.toOver) (b : Y'.toOver ⟶ Y.toOver)

def graphOpenAmbientMap : graphAmbient g ⟶ graphAmbient f :=
  pullback.map (g.left ≫ Y'.structureMap) Y'.structureMap (f.left ≫ Y.structureMap) Y.structureMap
    a.left b.left (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)
    ((Category.comp_id _).trans (g.w.trans
      ((congrArg (fun k => a.left ≫ k) f.w).trans a.w).symm))
    ((Category.comp_id _).trans b.w.symm)

theorem graphOpenAmbientMap_first :
    graphOpenAmbientMap f g a b ≫ graphFirstProjection f = graphFirstProjection g ≫ a.left :=
  pullback.lift_fst ..

theorem graphOpenAmbientMap_second :
    graphOpenAmbientMap f g a b ≫ graphSecondProjection f = graphSecondProjection g ≫ b.left :=
  pullback.lift_snd ..

instance graphOpenAmbientMap_open [IsOpenImmersion a.left] [IsOpenImmersion b.left] :
    IsOpenImmersion (graphOpenAmbientMap f g a b) := by
  exact @Scheme.pullback_map_isOpenImmersion X'.carrier Y'.carrier Foundations.Scheme.ProjectiveSpace.complexBase X.carrier Y.carrier Foundations.Scheme.ProjectiveSpace.complexBase
    (g.left ≫ Y'.structureMap) Y'.structureMap (f.left ≫ Y.structureMap) Y.structureMap
    a.left b.left (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)
    ((Category.comp_id _).trans (g.w.trans
      ((congrArg (fun k => a.left ≫ k) f.w).trans a.w).symm))
    ((Category.comp_id _).trans b.w.symm)
    (inferInstanceAs (IsOpenImmersion a.left)) (inferInstanceAs (IsOpenImmersion b.left)) inferInstance

theorem graphOpenAmbientMap_graph (h : a ≫ f = g ≫ b) :
    graph g ≫ graphOpenAmbientMap f g a b = a.left ≫ graph f := by
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => graph g ≫ k) (graphOpenAmbientMap_first f g a b)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ a.left) (graph_firstProjection g)).trans
            ((Category.id_comp _).trans
              ((Category.comp_id _).symm.trans
                ((congrArg (fun k => a.left ≫ k) (graph_firstProjection f)).symm.trans
                  (Category.assoc _ _ _).symm))))))
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => graph g ≫ k) (graphOpenAmbientMap_second f g a b)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ b.left) (graph_secondProjection g)).trans
            ((congrArg (fun k => k.left) h).symm.trans
              ((congrArg (fun k => a.left ≫ k) (graph_secondProjection f)).symm.trans
                (Category.assoc _ _ _).symm)))))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.OpenAmbient.BundleCycles
