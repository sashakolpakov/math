import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.MonoFamilyGluing
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Monomorphic Open To -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonomorphicOpenTo

noncomputable section

/-! Compatible monomorphic loci on an actual open cover glue along
their ambient fiber products. The compatibility data are maps between
specified local loci; the resulting scheme, Cartesian chart squares,
and geometry are constructed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

structure MonomorphicOpenCharts {S : Scheme.{u}} (M : Over S) (J : Type u) where
  base : J → Over S
  baseMap : ∀ j, base j ⟶ M
  baseMap_open : ∀ j, IsOpenImmersion (baseMap j).left
  covers : ∀ x : M.left, ∃ j, ∃ y : (base j).left, (baseMap j).left y = x
  chart : J → Over S
  chartMap : ∀ j, chart j ⟶ base j
  chartMap_mono : ∀ j, Mono (chartMap j)
  overlapLift : ∀ j k, pullback (chartMap j ≫ baseMap j) (baseMap k) ⟶ chart k
  overlapLift_map : ∀ j k, overlapLift j k ≫ chartMap k =
    pullback.snd (chartMap j ≫ baseMap j) (baseMap k)

attribute [instance] MonomorphicOpenCharts.baseMap_open MonomorphicOpenCharts.chartMap_mono

namespace MonomorphicOpenCharts
variable {S : Scheme.{u}} {M : Over S} {J : Type u} (C : MonomorphicOpenCharts M J)

instance baseMap_mono (j : J) : Mono (C.baseMap j) := Over.mono_of_mono_left _

abbrev toAmbient (j : J) : C.chart j ⟶ M := C.chartMap j ≫ C.baseMap j

instance toAmbient_mono (j : J) : Mono (C.toAmbient j) := by
  dsimp only [MonomorphicOpenCharts.toAmbient]
  infer_instance

/-- The supplied overlap lift identifies the full ambient intersection
with the restriction of the first chart to the second base open. -/
theorem overlap_isPullback (j k : J) :
    IsPullback (pullback.fst (C.toAmbient j) (C.baseMap k)) (C.overlapLift j k)
      (C.toAmbient j) (C.toAmbient k) := by
  have hsq : pullback.fst (C.toAmbient j) (C.baseMap k) ≫ C.toAmbient j =
      C.overlapLift j k ≫ C.toAmbient k := by
    exact (pullback.condition (f := C.toAmbient j) (g := C.baseMap k)).trans
      ((congrArg (fun r => r ≫ C.baseMap k) (C.overlapLift_map j k)).symm.trans
        (Category.assoc (C.overlapLift j k) (C.chartMap k) (C.baseMap k)))
  apply IsPullback.mk'
  · exact hsq
  · intro T a b hab _
    exact (cancel_mono (pullback.fst (C.toAmbient j) (C.baseMap k))).mp hab
  · intro T a b hab
    let x := pullback.lift a (b ≫ C.chartMap k)
      (hab.trans (Category.assoc b (C.chartMap k) (C.baseMap k)).symm)
    refine ⟨x, pullback.lift_fst _ _ _, ?_⟩
    apply (cancel_mono (C.chartMap k)).mp
    rw [Category.assoc, C.overlapLift_map]
    exact pullback.lift_snd _ _ _

instance intersection_open (j k : J) :
    IsOpenImmersion (pullback.fst (C.toAmbient j) (C.toAmbient k)).left := by
  let hp := C.overlap_isPullback j k
  let : IsOpenImmersion (pullback.fst (C.toAmbient j) (C.baseMap k)).left :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      ((IsPullback.of_hasPullback (C.toAmbient j) (C.baseMap k)).map (Over.forget S)).flip
      (C.baseMap_open k)
  let : IsIso hp.isoPullback.inv.left :=
    inferInstanceAs (IsIso ((Over.forget S).map hp.isoPullback.inv))
  have h : IsOpenImmersion (hp.isoPullback.inv.left ≫
      (pullback.fst (C.toAmbient j) (C.baseMap k)).left) := inferInstance
  have he := congrArg Over.Hom.left hp.isoPullback_inv_fst
  change hp.isoPullback.inv.left ≫
    (pullback.fst (C.toAmbient j) (C.baseMap k)).left = _ at he
  rw [he] at h
  exact h

instance intersection_snd_open (j k : J) :
    IsOpenImmersion (pullback.snd (C.toAmbient j) (C.toAmbient k)).left := by
  let e := pullbackSymmetry (C.toAmbient j) (C.toAmbient k)
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  have h : IsOpenImmersion (e.hom.left ≫
      (pullback.fst (C.toAmbient k) (C.toAmbient j)).left) := inferInstance
  have he := congrArg Over.Hom.left (pullbackSymmetry_hom_comp_fst (C.toAmbient j) (C.toAmbient k))
  change e.hom.left ≫ (pullback.fst (C.toAmbient k) (C.toAmbient j)).left = _ at he
  rw [he] at h
  exact h

/-- Actual scheme gluing data with canonical ambient-pullback
transition maps and their categorical cocycle. -/
def glueData : Scheme.GlueData :=
  HilbertScheme.Presentations.Relative.MonoFamilyGluing.relativeMonoFamilyGlueData M C.chart C.toAmbient

def scheme : Scheme.{u} := C.glueData.glued

def chartInclusion (j : J) : (C.chart j).left ⟶ C.scheme := C.glueData.ι j

instance chartInclusion_open (j : J) : IsOpenImmersion (C.chartInclusion j) :=
  Scheme.GlueData.ι_isOpenImmersion C.glueData j

def projection : C.scheme ⟶ M.left := HilbertScheme.Presentations.Relative.MonoFamilyGluing.relativeMonoFamilyParameter M C.chart C.toAmbient

theorem chart_projection (j : J) :
    C.chartInclusion j ≫ C.projection = (C.toAmbient j).left :=
  HilbertScheme.Presentations.Relative.MonoFamilyGluing.relativeMonoFamilyChart_parameter M C.chart C.toAmbient j

theorem chart_intersection (j k : J) :
    IsPullback (pullback.fst (C.toAmbient j) (C.toAmbient k)).left
      (pullback.snd (C.toAmbient j) (C.toAmbient k)).left
      (C.chartInclusion j) (C.chartInclusion k) :=
  HilbertScheme.Presentations.Relative.MonoFamilyGluing.relativeMonoFamilyChart_intersection M C.chart C.toAmbient j k

theorem chart_projection_apply (j : J) (x : (C.chart j).left) :
    C.projection (C.chartInclusion j x) = (C.baseMap j).left ((C.chartMap j).left x) := by
  simpa only [Scheme.Hom.comp_apply, MonomorphicOpenCharts.toAmbient, Over.comp_left] using
    congrArg (fun f : (C.chart j).left ⟶ M.left => f x) (C.chart_projection j)

theorem charts_cover (x : C.scheme) :
    ∃ j, ∃ y : (C.chart j).left, C.chartInclusion j y = x :=
  HilbertScheme.Presentations.Relative.MonoFamilyGluing.relativeMonoFamilyCharts_cover M C.chart C.toAmbient x

theorem projection_injective : Function.Injective C.projection :=
  HilbertScheme.Presentations.Relative.MonoFamilyGluing.relativeMonoFamilyParameter_injective M C.chart C.toAmbient

theorem chart_preimage (j : J) :
    C.projection ⁻¹ᵁ (C.baseMap j).left.opensRange = (C.chartInclusion j).opensRange := by
  ext x
  change C.projection x ∈ Set.range (C.baseMap j).left ↔ x ∈ Set.range (C.chartInclusion j)
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨k, y, rfl⟩ := C.charts_cover x
    have he : (C.toAmbient k).left y = (C.baseMap j).left v := by
      have hc : C.projection (C.chartInclusion k y) = (C.toAmbient k).left y := by
        simpa only [Scheme.Hom.comp_apply] using
          congrArg (fun f : (C.chart k).left ⟶ M.left => f y) (C.chart_projection k)
      exact hc.symm.trans hv.symm
    obtain ⟨z, _, hz⟩ := Scheme.exists_preimage_of_isPullback
      ((IsPullback.of_hasPullback (C.toAmbient k) (C.baseMap j)).map (Over.forget S)) y v he
    refine ⟨(C.overlapLift k j).left z, ?_⟩
    apply C.projection_injective
    rw [C.chart_projection_apply, C.chart_projection_apply]
    have hl : (C.chartMap j).left ((C.overlapLift k j).left z) = v := by
      have h : (C.overlapLift k j).left ≫ (C.chartMap j).left =
          (pullback.snd (C.toAmbient k) (C.baseMap j)).left :=
        congrArg Over.Hom.left (C.overlapLift_map k j)
      have h' : (C.chartMap j).left ((C.overlapLift k j).left z) =
          (pullback.snd (C.toAmbient k) (C.baseMap j)).left z :=
        (Scheme.Hom.comp_apply _ _ z).symm.trans
          (congrArg (fun f => f z) h)
      exact h'.trans hz
    rw [hl]
    simpa only [MonomorphicOpenCharts.toAmbient, Over.comp_left, Scheme.Hom.comp_apply] using he.symm
  · rintro ⟨y, rfl⟩
    exact ⟨(C.chartMap j).left y, (C.chart_projection_apply j y).symm⟩

/-- Each supplied local locus is exactly the pullback of the glued
scheme to its original base open. -/
theorem chart_isPullback (j : J) :
    IsPullback (C.chartInclusion j) (C.chartMap j).left C.projection (C.baseMap j).left :=
  (IsOpenImmersion.isPullback (C.chartMap j).left (C.chartInclusion j)
    (C.baseMap j).left C.projection (C.chart_projection j) (C.chart_preimage j)).flip

def baseCover : M.left.OpenCover.{u} :=
  Scheme.Cover.mkOfCovers J (fun j => (C.base j).left) (fun j => (C.baseMap j).left) C.covers

theorem projection_localProperty (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (hP : ∀ j, P (C.chartMap j).left) : P C.projection := by
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P := P) C.baseCover).mpr
  intro j
  change P (pullback.snd C.projection (C.baseMap j).left)
  let hp := C.chart_isPullback j
  rw [← hp.isoPullback_inv_snd, P.cancel_left_of_respectsIso]
  exact hP j

instance projection_mono : Mono C.projection :=
  C.projection_localProperty (MorphismProperty.monomorphisms Scheme)
    (fun j => Over.mono_left_of_mono (C.chartMap j))

instance projection_locallyOfFiniteType [∀ j, LocallyOfFiniteType (C.chartMap j).left] :
    LocallyOfFiniteType C.projection := by
  let : IsZariskiLocalAtTarget (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget
      (P := @LocallyOfFiniteType.{u}) (Q := RingHom.FiniteType)
  exact C.projection_localProperty (@LocallyOfFiniteType) (fun j => inferInstance)

instance projection_quasiCompact [∀ j, QuasiCompact (C.chartMap j).left] :
    QuasiCompact C.projection := by
  let : IsZariskiLocalAtTarget (@QuasiCompact.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat
  exact C.projection_localProperty (@QuasiCompact) (fun j => inferInstance)

def over : Over S := Over.mk (C.projection ≫ M.hom)

def inclusion : C.over ⟶ M := Over.homMk C.projection rfl

instance inclusion_left_mono : Mono C.inclusion.left := C.projection_mono

instance inclusion_mono : Mono C.inclusion := Over.mono_of_mono_left _

instance inclusion_locallyOfFiniteType [∀ j, LocallyOfFiniteType (C.chartMap j).left] :
    LocallyOfFiniteType C.inclusion.left := C.projection_locallyOfFiniteType

instance inclusion_quasiCompact [∀ j, QuasiCompact (C.chartMap j).left] :
    QuasiCompact C.inclusion.left := C.projection_quasiCompact

def chartOver (j : J) : C.chart j ⟶ C.over :=
  Over.homMk (C.chartInclusion j) (by
    change C.chartInclusion j ≫ (C.projection ≫ M.hom) = (C.chart j).hom
    rw [← Category.assoc, C.chart_projection]
    exact (C.toAmbient j).w)

theorem chartOver_inclusion (j : J) : C.chartOver j ≫ C.inclusion = C.toAmbient j :=
  Over.OverMorphism.ext (C.chart_projection j)

end MonomorphicOpenCharts

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonomorphicOpenTo
