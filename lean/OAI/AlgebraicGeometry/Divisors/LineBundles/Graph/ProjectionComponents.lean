import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.Chow
import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.IntegralGeometricFibers
import OAI.AlgebraicGeometry.Divisors.LineBundles.ClopenCoverBaseChange
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ImmersionNoetherian

/-! # Projection Components -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ProjectionComponents.BundleCycles

noncomputable section

/-! The actual graph ambient product splits into the disjoint products
with every integral component of its source. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

theorem projectiveComponents_cover (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    ∀ x : X.carrier, ∃! C : irreducibleComponents X.carrier, x ∈ Set.range (X.componentInclusion C) := by
  intro x
  let C : irreducibleComponents X.carrier :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  have hx : x ∈ Set.range (X.componentInclusion C) := by
    rw [X.componentInclusion_range]
    exact mem_irreducibleComponent
  refine ⟨C, hx, ?_⟩
  intro D hD
  by_contra hDC
  have hd : Disjoint (Set.range (X.componentInclusion D)) (Set.range (X.componentInclusion C)) :=
    TopologicalSpace.Opens.coe_disjoint.mpr
      (X.componentInclusionsOfStalkDomains_disjoint X.stalk_isDomain hDC)
  exact Set.disjoint_left.mp hd hD hx

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

def graphProjectionComponent (C : irreducibleComponents X.carrier) : Scheme :=
  pullback (X.componentInclusion C ≫ (f.left ≫ Y.structureMap)) Y.structureMap

def graphProjectionComponentInclusion (C : irreducibleComponents X.carrier) :
    graphProjectionComponent f C ⟶ OpenAmbient.BundleCycles.graphAmbient f :=
  Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap (f.left ≫ Y.structureMap)
    (X.componentInclusion C ≫ (f.left ≫ Y.structureMap)) (X.componentInclusion C) rfl Y.structureMap

def graphProjectionComponentMap (C : irreducibleComponents X.carrier) :
    graphProjectionComponent f C ⟶ Y.carrier :=
  pullback.snd (X.componentInclusion C ≫ (f.left ≫ Y.structureMap)) Y.structureMap

instance graphProjectionComponentInclusion_isOpenImmersion (C : irreducibleComponents X.carrier) :
    IsOpenImmersion (graphProjectionComponentInclusion f C) := by
  let : ∀ D, IsOpenImmersion (X.componentInclusion D) := fun D => X.componentInclusion_isOpenImmersion D
  let : ∀ D, IsClosedImmersion (X.componentInclusion D) := fun D => X.componentInclusion_isClosedImmersion D
  exact ClopenCoverBaseChange.BundleCycles.clopenCoverBaseChangeMap_isOpenImmersion
    (show X.carrier ⟶ Foundations.Scheme.ProjectiveSpace.complexBase from f.left ≫ Y.structureMap)
    (fun C => (X.componentVariety C).carrier) X.componentInclusion Y.structureMap C

instance graphProjectionComponentInclusion_isClosedImmersion (C : irreducibleComponents X.carrier) :
    IsClosedImmersion (graphProjectionComponentInclusion f C) := by
  let : IsClosedImmersion (X.componentInclusion C) := X.componentInclusion_isClosedImmersion C
  exact Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap_isClosedImmersion
    (show X.carrier ⟶ Foundations.Scheme.ProjectiveSpace.complexBase from f.left ≫ Y.structureMap)
    (X.componentInclusion C ≫ (show X.carrier ⟶ Foundations.Scheme.ProjectiveSpace.complexBase from f.left ≫ Y.structureMap))
    (X.componentInclusion C) rfl Y.structureMap

instance graphProjectionComponent_isNoetherian (C : irreducibleComponents X.carrier) :
    AlgebraicGeometry.IsNoetherian (graphProjectionComponent f C) :=
  Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian (graphProjectionComponentInclusion f C)

theorem graphProjectionComponent_over (C : irreducibleComponents X.carrier) :
    graphProjectionComponentInclusion f C ≫ OpenAmbient.BundleCycles.graphSecondProjection f = graphProjectionComponentMap f C :=
  Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap_snd _ _ _ _ _

instance graphProjectionComponentMap_smooth (C : irreducibleComponents X.carrier) :
    Smooth (graphProjectionComponentMap f C) := by
  have hb : (f.left ≫ Y.structureMap : X.carrier ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) = X.structureMap := f.w
  let : Smooth (X.componentInclusion C ≫ (f.left ≫ Y.structureMap)) := by
    change Smooth (X.componentInclusion C ≫ (show X.carrier ⟶ Foundations.Scheme.ProjectiveSpace.complexBase from f.left ≫ Y.structureMap))
    rw [hb]
    let : IsOpenImmersion (X.componentInclusion C) := X.componentInclusion_isOpenImmersion C
    infer_instance
  exact inferInstanceAs (Smooth (pullback.snd
    (X.componentInclusion C ≫ (f.left ≫ Y.structureMap)) Y.structureMap))

instance graphProjectionComponentMap_geometricallyIntegral (C : irreducibleComponents X.carrier) :
    GeometricallyIntegral (graphProjectionComponentMap f C) := by
  have hb : (f.left ≫ Y.structureMap : X.carrier ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) = X.structureMap := f.w
  let : GeometricallyIntegral (X.componentInclusion C ≫ (f.left ≫ Y.structureMap)) := by
    change GeometricallyIntegral (X.componentInclusion C ≫ (show X.carrier ⟶ Foundations.Scheme.ProjectiveSpace.complexBase from f.left ≫ Y.structureMap))
    rw [hb, X.componentInclusion_over]
    exact LineBundles.Smooth.IntegralGeometricFibers.BundleCycles.projectiveComponent_geometricallyIntegral X C
  exact inferInstanceAs (GeometricallyIntegral (pullback.snd
    (X.componentInclusion C ≫ (f.left ≫ Y.structureMap)) Y.structureMap))

theorem graphProjectionComponents_cover :
    ∀ x : OpenAmbient.BundleCycles.graphAmbient f, ∃! C, x ∈ Set.range (graphProjectionComponentInclusion f C) := by
  let : ∀ D, IsOpenImmersion (X.componentInclusion D) := fun D => X.componentInclusion_isOpenImmersion D
  let : ∀ D, IsClosedImmersion (X.componentInclusion D) := fun D => X.componentInclusion_isClosedImmersion D
  exact ClopenCoverBaseChange.BundleCycles.clopenCoverBaseChange_covers
    (show X.carrier ⟶ Foundations.Scheme.ProjectiveSpace.complexBase from f.left ≫ Y.structureMap)
    (fun C => (X.componentVariety C).carrier) X.componentInclusion Y.structureMap (projectiveComponents_cover X)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ProjectionComponents.BundleCycles
