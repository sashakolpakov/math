import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.OpenRepresentationLifts
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-! # Representation Atlas -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.PELModuli.IntegralModel.Reduced

/-! The triple-overlap maps of reduced local representations, with their
cocycle identity proved by the actual universal values. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable {S : Scheme.{0}} {F : (Over S)ᵒᵖ ⥤ Type} {U V W : S.Opens}
    (D : OpenRepresentations.ReducedOpenRepresentation F U) (E : OpenRepresentations.ReducedOpenRepresentation F V)
    (G : OpenRepresentations.ReducedOpenRepresentation F W)

def OpenRepresentations.ReducedOpenRepresentation.tripleLift {T : Over S} (f : T ⟶ D.overlap E) (g : T ⟶ D.overlap G) :
    T ⟶ E.overlap G :=
  E.overlapLift G (f ≫ D.comparison E ≫ E.inclusion D) (fun t => by
    have h := D.overlap_mapsTo_right G (g.left t)
    exact (congrArg (fun q : T.left ⟶ S => q t) g.w) ▸ h)

@[reassoc]
theorem OpenRepresentations.ReducedOpenRepresentation.tripleLift_inclusion {T : Over S} (f : T ⟶ D.overlap E) (g : T ⟶ D.overlap G) :
    D.tripleLift E G f g ≫ E.inclusion G = f ≫ D.comparison E ≫ E.inclusion D :=
  E.overlapLift_inclusion G _ _

def OpenRepresentations.ReducedOpenRepresentation.tripleMap : pullback (D.inclusion E) (D.inclusion G) ⟶
    pullback (E.inclusion G) (E.inclusion D) :=
  pullback.lift (D.tripleLift E G (pullback.fst _ _) (pullback.snd _ _))
    (pullback.fst _ _ ≫ D.comparison E) (by
      rw [OpenRepresentations.ReducedOpenRepresentation.tripleLift_inclusion, Category.assoc])

@[reassoc]
theorem OpenRepresentations.ReducedOpenRepresentation.tripleMap_snd : D.tripleMap E G ≫ pullback.snd _ _ =
    pullback.fst _ _ ≫ D.comparison E := pullback.lift_snd _ _ _

@[reassoc]
theorem OpenRepresentations.ReducedOpenRepresentation.tripleMap_fst_inclusion : D.tripleMap E G ≫ pullback.fst _ _ ≫ E.inclusion G =
    pullback.fst _ _ ≫ D.comparison E ≫ E.inclusion D := by
  rw [← Category.assoc, OpenRepresentations.ReducedOpenRepresentation.tripleMap, pullback.lift_fst, OpenRepresentations.ReducedOpenRepresentation.tripleLift_inclusion]

theorem OpenRepresentations.ReducedOpenRepresentation.tripleMap_value {T : Over S}
    (f : T ⟶ pullback (D.inclusion E) (D.inclusion G)) :
    F.map (f ≫ D.tripleMap E G ≫ pullback.fst _ _ ≫ E.inclusion G).op E.sectionValue =
      F.map (f ≫ pullback.fst _ _ ≫ D.inclusion E).op D.sectionValue := by
  rw [OpenRepresentations.ReducedOpenRepresentation.tripleMap_fst_inclusion]
  simp only [op_comp, F.map_comp, types_comp_apply, OpenRepresentations.ReducedOpenRepresentation.comparison_value]

instance OpenRepresentations.ReducedOpenRepresentation.triple_reduced : IsReduced (pullback (D.inclusion E) (D.inclusion G)).left := by
  let p := pullback.fst (D.inclusion E) (D.inclusion G)
  have : IsOpenImmersion p.left := MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback (D.inclusion E) (D.inclusion G)).map (Over.forget S)).flip
    (D.inclusion_open G)
  exact isReduced_of_isOpenImmersion p.left

theorem OpenRepresentations.ReducedOpenRepresentation.tripleMap_cocycle :
    D.tripleMap E G ≫ E.tripleMap G D ≫ G.tripleMap D E = 𝟙 _ := by
  apply (cancel_mono (pullback.fst (D.inclusion E) (D.inclusion G))).mp
  apply (cancel_mono (D.inclusion E)).mp
  apply D.hom_ext
  simp only [Category.assoc, Category.id_comp]
  rw [← Category.assoc (D.tripleMap E G), OpenRepresentations.ReducedOpenRepresentation.tripleMap_value,
    Category.assoc, OpenRepresentations.ReducedOpenRepresentation.tripleMap_value]
  simpa only [Category.id_comp] using D.tripleMap_value E G (𝟙 _)

end AlgebraicGeometry.PELModuli.IntegralModel.Reduced

namespace AlgebraicGeometry.PELModuli.IntegralModel.Reduced.RepresentationAtlas
section

/-! The actual scheme atlas obtained from local representations on reduced
tests. The transition maps and cocycle are constructed, rather than inputs. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

namespace ReducedRepresentationAtlas
variable {S : Scheme.{0}} {F : (Over S)ᵒᵖ ⥤ Type} {I : Type} {U : I → S.Opens}
    (D : ∀ i, OpenRepresentations.ReducedOpenRepresentation F (U i))

def glueDataOver : CategoryTheory.GlueData (Over S) where
  J := I
  U i := (D i).space
  V p := (D p.1).overlap (D p.2)
  f i j := (D i).inclusion (D j)
  t i j := (D i).comparison (D j)
  t_id i := (D i).comparison_self
  t' i j k := (D i).tripleMap (D j) (D k)
  t_fac i j k := (D i).tripleMap_snd (D j) (D k)
  cocycle i j k := (D i).tripleMap_cocycle (D j) (D k)

def glueData : Scheme.GlueData where
  toGlueData := (glueDataOver D).mapGlueData (Over.forget S)
  f_open i j := (D i).inclusion_open (D j)

def scheme : Scheme := (glueData D).glued

def chart (i : I) : (D i).space.left ⟶ scheme D := (glueData D).ι i

instance chart_open (i : I) : IsOpenImmersion (chart D i) :=
  Scheme.GlueData.ι_isOpenImmersion (glueData D) i

def structureMap : scheme D ⟶ S := by
  fapply Multicoequalizer.desc
  · exact fun i => (D i).space.hom
  rintro ⟨i, j⟩
  change ((D i).inclusion (D j)).left ≫ (D i).space.hom =
    (((D i).comparison (D j)).left ≫ ((D j).inclusion (D i)).left) ≫ (D j).space.hom
  rw [Category.assoc, ((D i).inclusion (D j)).w, ((D j).inclusion (D i)).w,
    ((D i).comparison (D j)).w]

@[reassoc]
theorem chart_structureMap (i : I) : chart D i ≫ structureMap D = (D i).space.hom :=
  Multicoequalizer.π_desc _ _ _ _ _

def over : Over S := Over.mk (structureMap D)

def chartOver (i : I) : (D i).space ⟶ over D :=
  Over.homMk (chart D i) (chart_structureMap D i)

theorem charts_cover (z : scheme D) : ∃ i, ∃ x : (D i).space.left, chart D i x = z :=
  (glueData D).ι_jointly_surjective z

def openCover : (scheme D).OpenCover := (glueData D).openCover

instance reduced : IsReduced (scheme D) := by
  have (i : I) : IsReduced ((ReducedRepresentationAtlas.openCover D).X i) := (D i).reduced
  exact IsReduced.of_openCover (scheme D) (𝒰 := ReducedRepresentationAtlas.openCover D)

theorem chart_intersection (i j : I) :
    IsPullback ((D i).inclusion (D j)).left
      (((D i).comparison (D j)).left ≫ ((D j).inclusion (D i)).left)
      (chart D i) (chart D j) :=
  IsPullback.of_isLimit ((glueData D).vPullbackConeIsLimit i j)

theorem chart_glue (i j : I) :
    ((D i).comparison (D j)).left ≫ ((D j).inclusion (D i)).left ≫ chart D j =
      ((D i).inclusion (D j)).left ≫ chart D i := (glueData D).glue_condition i j

end ReducedRepresentationAtlas

end

section

/-! Each glued parameter chart is the full inverse image of its base open. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

namespace ReducedRepresentationAtlas
variable {S : Scheme.{0}} {F : (Over S)ᵒᵖ ⥤ Type} {I : Type} {U : I → S.Opens}
    (D : ∀ i, OpenRepresentations.ReducedOpenRepresentation F (U i))

theorem chart_range (i : I) : Set.range (chart D i) =
    (structureMap D) ⁻¹' (U i : Set S) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    change structureMap D (chart D i x) ∈ U i
    have h : structureMap D (chart D i x) = (D i).space.hom x :=
      congrArg (fun q : (D i).space.left ⟶ S => q x) (chart_structureMap D i)
    exact h ▸ (D i).mapsTo x
  · intro hz
    obtain ⟨j, x, rfl⟩ := charts_cover D z
    have hx : (D j).space.hom x ∈ U i := by
      have h : structureMap D (chart D j x) = (D j).space.hom x :=
        congrArg (fun q : (D j).space.left ⟶ S => q x) (chart_structureMap D j)
      exact h ▸ hz
    let y : ((D j).overlap (D i)).left := ⟨x, hx⟩
    refine ⟨((D i).inclusion (D j)).left (((D j).comparison (D i)).left y), ?_⟩
    exact congrArg (fun q : ((D j).overlap (D i)).left ⟶ scheme D => q y)
      (chart_glue D j i)

theorem chart_opensRange (i : I) : (chart D i).opensRange = structureMap D ⁻¹ᵁ U i :=
  TopologicalSpace.Opens.coe_inj.mp (chart_range D i)

def chartBase (i : I) : (D i).space.left ⟶ (U i).toScheme :=
  IsOpenImmersion.lift (U i).ι (D i).space.hom (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact (D i).mapsTo x)

@[reassoc]
theorem chartBase_ι (i : I) : chartBase D i ≫ (U i).ι = (D i).space.hom :=
  IsOpenImmersion.lift_fac _ _ _

theorem chart_isPullback (i : I) :
    IsPullback (chartBase D i) (chart D i) (U i).ι (structureMap D) := by
  refine ⟨⟨by rw [chartBase_ι, chart_structureMap]⟩,
    ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro c
    apply IsOpenImmersion.lift (chart D i) c.snd
    rw [chart_range]
    rintro _ ⟨x, rfl⟩
    change structureMap D (c.snd x) ∈ U i
    have h : structureMap D (c.snd x) = (U i).ι (c.fst x) :=
      congrArg (fun q : c.pt ⟶ S => q x) c.condition.symm
    exact h ▸ (c.fst x).property
  · intro c
    rw [← cancel_mono (U i).ι, Category.assoc, chartBase_ι,
      ← chart_structureMap D i, IsOpenImmersion.lift_fac_assoc, c.condition]
  · intro c
    exact IsOpenImmersion.lift_fac _ _ _
  · intro c m _ h2
    apply (cancel_mono (chart D i)).mp
    rw [IsOpenImmersion.lift_fac]
    exact h2

end ReducedRepresentationAtlas

end

/-! Once a global universal value restricts to the local universal values,
its classifier is bijective on every reduced test contained in a base chart. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

namespace ReducedRepresentationAtlas
variable {S : Scheme.{0}} {F : (Over S)ᵒᵖ ⥤ Type} {I : Type} {U : I → S.Opens}
    (D : ∀ i, OpenRepresentations.ReducedOpenRepresentation F (U i))

instance chartOver_mono (i : I) : Mono (chartOver D i) :=
  (Over.forget S).mono_of_mono_map (show Mono (chartOver D i).left from inferInstanceAs (Mono (chart D i)))

def factorToChart (i : I) {T : Over S} (hT : ∀ t : T.left, T.hom t ∈ U i)
    (f : T ⟶ over D) : T ⟶ (D i).space := by
  have hr : Set.range f.left ⊆ Set.range (chart D i) := by
    rw [chart_range]
    rintro _ ⟨t, rfl⟩
    change structureMap D (f.left t) ∈ U i
    have ht : structureMap D (f.left t) = T.hom t := congrArg (fun q : T.left ⟶ S => q t) f.w
    exact ht ▸ hT t
  let q := IsOpenImmersion.lift (chart D i) f.left hr
  refine Over.homMk q ?_
  rw [← chart_structureMap D i, IsOpenImmersion.lift_fac_assoc]
  exact f.w

theorem factorToChart_chart (i : I) {T : Over S} (hT : ∀ t : T.left, T.hom t ∈ U i)
    (f : T ⟶ over D) : factorToChart D i hT f ≫ chartOver D i = f := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

def chartHomEquiv (i : I) (T : Over S) (hT : ∀ t : T.left, T.hom t ∈ U i) :
    (T ⟶ over D) ≃ (T ⟶ (D i).space) where
  toFun := factorToChart D i hT
  invFun f := f ≫ chartOver D i
  left_inv := factorToChart_chart D i hT
  right_inv f := (cancel_mono (chartOver D i)).mp (factorToChart_chart D i hT (f ≫ chartOver D i))

theorem classifies_on_base_open (u : F.obj (op (over D))) (i : I)
    (hu : F.map (chartOver D i).op u = (D i).sectionValue)
    (T : Over S) [IsReduced T.left] (hT : ∀ t : T.left, T.hom t ∈ U i) :
    Function.Bijective (fun f : T ⟶ over D => F.map f.op u) := by
  have hb := ((D i).classifies T hT).comp (chartHomEquiv D i T hT).bijective
  convert hb using 1
  funext f
  change F.map f.op u = F.map (factorToChart D i hT f).op (D i).sectionValue
  rw [← hu, ← F.map_comp_apply]
  exact congrArg (fun q : T ⟶ over D => F.map q.op u) (factorToChart_chart D i hT f).symm

end ReducedRepresentationAtlas

end AlgebraicGeometry.PELModuli.IntegralModel.Reduced.RepresentationAtlas

end

end OAI
