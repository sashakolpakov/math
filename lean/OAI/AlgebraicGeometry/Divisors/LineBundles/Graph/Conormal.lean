import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.Chow
import OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.TopDegree
import OAI.AlgebraicGeometry.Betti.Scheme

/-! # Conormal -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.Conormal.BundleCycles

noncomputable section

section

/-! The actual graph center and normal-cone isomorphism, with
their commuting structure maps and genuine conormal bundle charts. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

instance graphConeStructureMap_locallyOfFiniteType : LocallyOfFiniteType (Chow.BundleCycles.graphConeStructureMap f) := by
  unfold Chow.BundleCycles.graphConeStructureMap
  infer_instance

instance graphNormalProjection_smooth : Smooth (Chow.BundleCycles.graphNormalProjection f) :=
  GraphNormal.ConeProperties.BundleCycles.graphNormalConeProjection_smooth f

instance graphAmbient_isSeparated : (OpenAmbient.BundleCycles.graphAmbient f).IsSeparated := ⟨by
  let : IsProper X.structureMap := X.projective.isProper
  rw [← Limits.terminal.comp_from (OpenAmbient.BundleCycles.graphFirstProjection f ≫ X.structureMap)]
  infer_instance⟩

def graphCenterStructureMap : (OpenAmbient.BundleCycles.graph f).ker.subscheme ⟶ Foundations.Scheme.ProjectiveSpace.complexBase :=
  inv (OpenAmbient.BundleCycles.graph f).toImage ≫ X.structureMap

instance graphCenterStructureMap_locallyOfFiniteType : LocallyOfFiniteType (graphCenterStructureMap f) := by
  unfold graphCenterStructureMap
  infer_instance

theorem graphToCenter_structure : (OpenAmbient.BundleCycles.graph f).toImage ≫ graphCenterStructureMap f = X.structureMap := by
  unfold graphCenterStructureMap
  rw [IsIso.hom_inv_id_assoc]

theorem graphConormalCenter_hasAffineSpaceCharts : Affine.SpaceChartBaseChange.BundleCycles.HasAffineSpaceCharts (Conormal.SupportCover.BundleCycles.globalConormalToSupport (OpenAmbient.BundleCycles.graph f).ker) :=
  Affine.SpaceChartBaseChange.BundleCycles.hasAffineSpaceCharts_of_specCharts _
    (Global.SectionAffineSpaceCharts.BundleCycles.globalSection_exists_affineSpaceChart (OpenAmbient.BundleCycles.graphFirstProjection f) (OpenAmbient.BundleCycles.graph f) (OpenAmbient.BundleCycles.graph_firstProjection f))

instance graphConormalCenter_smooth : Smooth (Conormal.SupportCover.BundleCycles.globalConormalToSupport (OpenAmbient.BundleCycles.graph f).ker) :=
  (graphConormalCenter_hasAffineSpaceCharts f).smooth

instance graphConormalCenter_geometricallyIntegral : GeometricallyIntegral (Conormal.SupportCover.BundleCycles.globalConormalToSupport (OpenAmbient.BundleCycles.graph f).ker) :=
  (graphConormalCenter_hasAffineSpaceCharts f).geometricallyIntegral

theorem graphNormalConeEquiv_center_square :
    Chow.BundleCycles.graphNormalProjection f ≫ (OpenAmbient.BundleCycles.graph f).toImage =
      (Global.GraphNormalCone.BundleCycles.graphNormalConeEquiv f).hom ≫ Conormal.SupportCover.BundleCycles.globalConormalToSupport (OpenAmbient.BundleCycles.graph f).ker := by
  change (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection (OpenAmbient.BundleCycles.graph f).ker ≫ OpenAmbient.BundleCycles.graphFirstProjection f) ≫ (OpenAmbient.BundleCycles.graph f).toImage = _
  rw [← Global.GraphNormalCone.BundleCycles.graphNormalConeEquiv_toSource, Category.assoc, ← AffineSpaceCharts.BundleCycles.graphConormalProjection_support,
    Category.assoc, IsIso.inv_hom_id, Category.comp_id]

theorem graphNormalConeEquiv_center_isPullback :
    IsPullback (Chow.BundleCycles.graphNormalProjection f) (Global.GraphNormalCone.BundleCycles.graphNormalConeEquiv f).hom
      (OpenAmbient.BundleCycles.graph f).toImage (Conormal.SupportCover.BundleCycles.globalConormalToSupport (OpenAmbient.BundleCycles.graph f).ker) :=
  IsPullback.of_vert_isIso ⟨graphNormalConeEquiv_center_square f⟩

theorem graphNormalConeEquiv_structure :
    (Global.GraphNormalCone.BundleCycles.graphNormalConeEquiv f).hom ≫ (Conormal.SupportCover.BundleCycles.globalConormalToSupport (OpenAmbient.BundleCycles.graph f).ker ≫ graphCenterStructureMap f) =
      Chow.BundleCycles.graphConeStructureMap f := by
  rw [← Category.assoc, ← graphNormalConeEquiv_center_square, Category.assoc,
    graphToCenter_structure, Chow.BundleCycles.graphConeStructureMap_normal]

end

section

/-! The normal-cone projection factors through the actual graph; this
identifies its first and second ambient component labels. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

theorem graphNormalProjection_graph :
    Chow.BundleCycles.graphNormalProjection f ≫ OpenAmbient.BundleCycles.graph f = Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection (OpenAmbient.BundleCycles.graph f).ker := by
  have H := congrArg (fun a => a ≫ OpenAmbient.BundleCycles.graph f) (Global.GraphNormalCone.BundleCycles.graphNormalConeEquiv_toSource f)
  rw [Category.assoc, Global.GraphNormalCone.BundleCycles.graphConormalProjection_toAmbient] at H
  have hb : (Global.GraphNormalCone.BundleCycles.graphNormalConeEquiv f).hom ≫ Conormal.DiagramGluing.BundleCycles.globalConormalSpectrumProjection (OpenAmbient.BundleCycles.graph f).ker =
      Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection (OpenAmbient.BundleCycles.graph f).ker := Global.NormalConeEmbedding.BundleCycles.globalNormalConeToConormal_toBase (OpenAmbient.BundleCycles.graph f).ker
  exact H.symm.trans hb

theorem graphCone_secondProjection :
    Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection (OpenAmbient.BundleCycles.graph f).ker ≫ OpenAmbient.BundleCycles.graphSecondProjection f =
      Chow.BundleCycles.graphNormalProjection f ≫ f.left := by
  rw [← graphNormalProjection_graph, Category.assoc, OpenAmbient.BundleCycles.graph_secondProjection]
  rfl

end

/-! The actual graph and normal-cone maps are morphisms over the
complex base. Singular pullback respects their proved factorizations. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem bettiMap_comp {R : Type} [Ring R] (M : ModuleCat R) (n : ℕ)
    {A B C : Over Foundations.Scheme.ProjectiveSpace.complexBase} (u : A ⟶ B) (v : B ⟶ C) :
    Betti.Scheme.schemeBettiMap M n (u ≫ v) = Betti.Scheme.schemeBettiMap M n v ≫ Betti.Scheme.schemeBettiMap M n u :=
  (Betti.Scheme.schemeBettiFunctor M n).map_comp v.op u.op

theorem bettiMap_id {R : Type} [Ring R] (M : ModuleCat R) (n : ℕ) (A : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    Betti.Scheme.schemeBettiMap M n (𝟙 A) = 𝟙 (Betti.Scheme.schemeBetti M A n) :=
  (Betti.Scheme.schemeBettiFunctor M n).map_id (Opposite.op A)

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

def graphAmbientOver : Over Foundations.Scheme.ProjectiveSpace.complexBase := Over.mk (Chow.BundleCycles.graphAmbientStructureMap f)

def graphConeOver : Over Foundations.Scheme.ProjectiveSpace.complexBase := Over.mk (Chow.BundleCycles.graphConeStructureMap f)

def graphFirstProjectionOver : graphAmbientOver f ⟶ X.toOver :=
  Over.homMk (OpenAmbient.BundleCycles.graphFirstProjection f) (Chow.BundleCycles.graphAmbientStructureMap_first f)

def graphSecondProjectionOver : graphAmbientOver f ⟶ Y.toOver :=
  Over.homMk (OpenAmbient.BundleCycles.graphSecondProjection f) rfl

def graphOver : X.toOver ⟶ graphAmbientOver f :=
  Over.homMk (OpenAmbient.BundleCycles.graph f) (by
    change OpenAmbient.BundleCycles.graph f ≫ (OpenAmbient.BundleCycles.graphSecondProjection f ≫ Y.structureMap) = X.structureMap
    rw [← Category.assoc, OpenAmbient.BundleCycles.graph_secondProjection]
    exact f.w)

def graphNormalProjectionOver : graphConeOver f ⟶ X.toOver :=
  Over.homMk (Chow.BundleCycles.graphNormalProjection f) (Chow.BundleCycles.graphConeStructureMap_normal f)

def graphConeToAmbientOver : graphConeOver f ⟶ graphAmbientOver f :=
  Over.homMk (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection (OpenAmbient.BundleCycles.graph f).ker) rfl

theorem graphOver_secondProjection : graphOver f ≫ graphSecondProjectionOver f = f := by
  apply Over.OverMorphism.ext
  exact OpenAmbient.BundleCycles.graph_secondProjection f

theorem graphNormalProjectionOver_graph :
    graphNormalProjectionOver f ≫ graphOver f = graphConeToAmbientOver f := by
  apply Over.OverMorphism.ext
  exact graphNormalProjection_graph f

theorem graphConeToAmbientOver_secondProjection :
    graphConeToAmbientOver f ≫ graphSecondProjectionOver f = graphNormalProjectionOver f ≫ f := by
  apply Over.OverMorphism.ext
  exact graphCone_secondProjection f

theorem graphBetti_factorization (n : ℕ) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) n f =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) n (graphSecondProjectionOver f) ≫
        Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) n (graphOver f) := by
  rw [← bettiMap_comp, graphOver_secondProjection]

theorem graphConeBetti_factorization (n : ℕ) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) n f ≫ Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) n (graphNormalProjectionOver f) =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) n (graphSecondProjectionOver f) ≫
        Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) n (graphConeToAmbientOver f) := by
  rw [← bettiMap_comp, ← bettiMap_comp, graphConeToAmbientOver_secondProjection]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.Conormal.BundleCycles
