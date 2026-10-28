import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.Intersections
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.MonoFamilyGluing

/-! # Data -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.Data.GradedHilbert

noncomputable section

/-! The bounded Hilbert charts glue to an actual scheme mapping
monomorphically to the Grassmannian. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] (n N : ℕ) (S : Scheme.{u}) (q : ℕ → ℕ)

instance normalizedHilbertChartParameter_isImmersion (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) :
    IsImmersion (NormalizedHilbert.OpenOverlap.GradedHilbert.normalizedHilbertChartParameter a S q).left := by
  change IsImmersion ((NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartInclusion a S q).left ≫ Grassmannian.Gluing.grassmannianChartMap a S)
  infer_instance

def boundedHilbertGlueData : Scheme.GlueData :=
  Relative.MonoFamilyGluing.relativeMonoFamilyGlueData (Grassmannian.Gluing.grassmannianOver (ι := ι) (ν := Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) S)
    (fun a => NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart a S q) (fun a => NormalizedHilbert.OpenOverlap.GradedHilbert.normalizedHilbertChartParameter a S q)

def boundedHilbertScheme : Scheme.{u} := (boundedHilbertGlueData (ι := ι) n N S q).glued

def boundedHilbertChartMap (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) :
    (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart a S q).left ⟶ boundedHilbertScheme (ι := ι) n N S q :=
  (boundedHilbertGlueData (ι := ι) n N S q).ι a

instance boundedHilbertChartMap_isOpenImmersion (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) :
    IsOpenImmersion (boundedHilbertChartMap n N S q a) :=
  Scheme.GlueData.ι_isOpenImmersion (boundedHilbertGlueData (ι := ι) n N S q) a

def boundedHilbertParameter : boundedHilbertScheme (ι := ι) n N S q ⟶
    Grassmannian.Gluing.grassmannianScheme (ι := ι) (ν := Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) S :=
  Relative.MonoFamilyGluing.relativeMonoFamilyParameter (Grassmannian.Gluing.grassmannianOver (ι := ι) (ν := Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) S)
    (fun a => NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart a S q) (fun a => NormalizedHilbert.OpenOverlap.GradedHilbert.normalizedHilbertChartParameter a S q)

theorem boundedHilbertChartMap_parameter (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) :
    boundedHilbertChartMap n N S q a ≫ boundedHilbertParameter (ι := ι) n N S q =
      (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartInclusion a S q).left ≫ Grassmannian.Gluing.grassmannianChartMap a S :=
  Relative.MonoFamilyGluing.relativeMonoFamilyChart_parameter _ _ _ a

instance boundedHilbertParameter_mono : Mono (boundedHilbertParameter (ι := ι) n N S q) :=
  Relative.MonoFamilyGluing.relativeMonoFamilyParameter_mono _ _ _

instance boundedHilbertParameter_locallyOfFiniteType :
    LocallyOfFiniteType (boundedHilbertParameter (ι := ι) n N S q) := by
  have : IsZariskiLocalAtSource @LocallyOfFiniteType.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType.{u}) (Q := RingHom.FiniteType)
  apply (IsZariskiLocalAtSource.iff_of_openCover
    (P := @LocallyOfFiniteType) (boundedHilbertGlueData (ι := ι) n N S q).openCover).mpr
  intro a
  change ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N at a
  change LocallyOfFiniteType (boundedHilbertChartMap n N S q a ≫ boundedHilbertParameter n N S q)
  rw [boundedHilbertChartMap_parameter]
  exact inferInstanceAs (LocallyOfFiniteType (NormalizedHilbert.OpenOverlap.GradedHilbert.normalizedHilbertChartParameter a S q).left)

def boundedHilbertOver : Over S :=
  Over.mk (boundedHilbertParameter (ι := ι) n N S q ≫
    Grassmannian.Gluing.grassmannianStructureMap (ι := ι) (ν := Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) S)

def boundedHilbertParameterOver : boundedHilbertOver (ι := ι) n N S q ⟶
    Grassmannian.Gluing.grassmannianOver (ι := ι) (ν := Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) S :=
  Over.homMk (boundedHilbertParameter (ι := ι) n N S q) rfl

instance boundedHilbertParameterOver_mono : Mono (boundedHilbertParameterOver (ι := ι) n N S q) := by
  have : Mono (boundedHilbertParameterOver (ι := ι) n N S q).left := boundedHilbertParameter_mono n N S q
  exact Over.mono_of_mono_left _

theorem boundedHilbertCharts_cover (x : boundedHilbertScheme (ι := ι) n N S q) :
    ∃ a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N, ∃ y : (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart a S q).left,
      boundedHilbertChartMap n N S q a y = x :=
  (boundedHilbertGlueData (ι := ι) n N S q).ι_jointly_surjective x

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.Data.GradedHilbert
