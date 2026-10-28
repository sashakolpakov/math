import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.RepresentationLifts
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-! # Representation Atlas Is -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily

/-! The triple-overlap maps of local representations, with their
cocycle identity proved by the actual universal values. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable {S : Scheme.{0}} {F : (Over S)ᵒᵖ ⥤ Type} {U V W : S.Opens}
    (D : Open.Representations.OpenRepresentation F U) (E : Open.Representations.OpenRepresentation F V)
    (G : Open.Representations.OpenRepresentation F W)

def Open.Representations.OpenRepresentation.tripleLift {T : Over S} (f : T ⟶ D.overlap E) (g : T ⟶ D.overlap G) :
    T ⟶ E.overlap G :=
  E.overlapLift G (f ≫ D.comparison E ≫ E.inclusion D) (fun t => by
    have h := D.overlap_mapsTo_right G (g.left t)
    exact (congrArg (fun q : T.left ⟶ S => q t) g.w) ▸ h)

@[reassoc]
theorem Open.Representations.OpenRepresentation.tripleLift_inclusion {T : Over S} (f : T ⟶ D.overlap E) (g : T ⟶ D.overlap G) :
    D.tripleLift E G f g ≫ E.inclusion G = f ≫ D.comparison E ≫ E.inclusion D :=
  E.overlapLift_inclusion G _ _

def Open.Representations.OpenRepresentation.tripleMap : pullback (D.inclusion E) (D.inclusion G) ⟶
    pullback (E.inclusion G) (E.inclusion D) :=
  pullback.lift (D.tripleLift E G (pullback.fst _ _) (pullback.snd _ _))
    (pullback.fst _ _ ≫ D.comparison E) (by
      rw [Open.Representations.OpenRepresentation.tripleLift_inclusion, Category.assoc])

@[reassoc]
theorem Open.Representations.OpenRepresentation.tripleMap_snd : D.tripleMap E G ≫ pullback.snd _ _ =
    pullback.fst _ _ ≫ D.comparison E := pullback.lift_snd _ _ _

@[reassoc]
theorem Open.Representations.OpenRepresentation.tripleMap_fst_inclusion : D.tripleMap E G ≫ pullback.fst _ _ ≫ E.inclusion G =
    pullback.fst _ _ ≫ D.comparison E ≫ E.inclusion D := by
  rw [← Category.assoc, Open.Representations.OpenRepresentation.tripleMap, pullback.lift_fst, Open.Representations.OpenRepresentation.tripleLift_inclusion]

theorem Open.Representations.OpenRepresentation.tripleMap_value {T : Over S}
    (f : T ⟶ pullback (D.inclusion E) (D.inclusion G)) :
    F.map (f ≫ D.tripleMap E G ≫ pullback.fst _ _ ≫ E.inclusion G).op E.sectionValue =
      F.map (f ≫ pullback.fst _ _ ≫ D.inclusion E).op D.sectionValue := by
  rw [Open.Representations.OpenRepresentation.tripleMap_fst_inclusion]
  simp only [op_comp, F.map_comp, types_comp_apply, Open.Representations.OpenRepresentation.comparison_value]

theorem Open.Representations.OpenRepresentation.tripleMap_cocycle :
    D.tripleMap E G ≫ E.tripleMap G D ≫ G.tripleMap D E = 𝟙 _ := by
  apply (cancel_mono (pullback.fst (D.inclusion E) (D.inclusion G))).mp
  apply (cancel_mono (D.inclusion E)).mp
  apply D.hom_ext
  simp only [Category.assoc, Category.id_comp]
  rw [← Category.assoc (D.tripleMap E G), Open.Representations.OpenRepresentation.tripleMap_value,
    Category.assoc, Open.Representations.OpenRepresentation.tripleMap_value]
  simpa only [Category.id_comp] using D.tripleMap_value E G (𝟙 _)

end AlgebraicGeometry.AbelianModuli.ReferenceFamily

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentationAtlasIs.RepresentationAtlas
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
section

/-! The actual scheme atlas obtained from local representations on arbitrary
tests. The transition maps and cocycle are constructed, rather than inputs. -/

open Opposite

variable {S : Scheme.{0}} {F : (Over S)ᵒᵖ ⥤ Type} {I : Type} {U : I → S.Opens}
    (D : ∀ i, Open.Representations.OpenRepresentation F (U i))

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

theorem chart_intersection (i j : I) :
    IsPullback ((D i).inclusion (D j)).left
      (((D i).comparison (D j)).left ≫ ((D j).inclusion (D i)).left)
      (chart D i) (chart D j) :=
  IsPullback.of_isLimit ((glueData D).vPullbackConeIsLimit i j)

theorem chart_glue (i j : I) :
    ((D i).comparison (D j)).left ≫ ((D j).inclusion (D i)).left ≫ chart D j =
      ((D i).inclusion (D j)).left ≫ chart D i := (glueData D).glue_condition i j

end

section

/-! Each glued parameter chart is the full inverse image of its base open. -/

open Opposite

variable {S : Scheme.{0}} {F : (Over S)ᵒᵖ ⥤ Type} {I : Type} {U : I → S.Opens}
    (D : ∀ i, Open.Representations.OpenRepresentation F (U i))

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

end

/-! The actual local universal values agree on every test of the glued
atlas intersection, by the constructed cartesian intersection square. -/

open Opposite

variable {S : Scheme.{0}} {F : (Over S)ᵒᵖ ⥤ Type} {I : Type} {U : I → S.Opens}
    (D : ∀ i, Open.Representations.OpenRepresentation F (U i))

theorem chart_intersection_over (i j : I) :
    IsPullback ((D i).inclusion (D j))
      ((D i).comparison (D j) ≫ (D j).inclusion (D i)) (chartOver D i) (chartOver D j) := by
  apply IsPullback.of_map_of_faithful (Over.forget S)
  exact chart_intersection D i j

theorem localValues_match (i j : I) {T : Over S} (f : T ⟶ (D i).space) (g : T ⟶ (D j).space)
    (h : f ≫ chartOver D i = g ≫ chartOver D j) :
    F.map f.op (D i).sectionValue = F.map g.op (D j).sectionValue := by
  let H := chart_intersection_over D i j
  let q := H.lift f g h
  have hf : q ≫ (D i).inclusion (D j) = f := H.lift_fst f g h
  have hg : q ≫ (D i).comparison (D j) ≫ (D j).inclusion (D i) = g := H.lift_snd f g h
  rw [← hf, ← hg]
  simp only [op_comp, F.map_comp, types_comp_apply, Open.Representations.OpenRepresentation.comparison_value]

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentationAtlasIs.RepresentationAtlas

end

end OAI
