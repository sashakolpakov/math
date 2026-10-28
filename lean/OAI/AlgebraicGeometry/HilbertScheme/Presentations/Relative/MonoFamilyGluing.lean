import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MonoFamilyGlueData
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-! # Mono Family Gluing -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.MonoFamilyGluing

noncomputable section

/-! Gluing relative subobjects with open pairwise intersections. All chart
intersections remain the actual ambient fiber products. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {J : Type u} (M : Over S) (U : J → Over S) (f : ∀ i, U i ⟶ M)
variable [∀ i, Mono (f i)]
variable [hopen : ∀ i j, IsOpenImmersion (pullback.fst (f i) (f j)).left]

def relativeMonoFamilyGlueData : Scheme.GlueData where
  toGlueData := (MonoFamilyGlueData.monoFamilyGlueData U f).mapGlueData (Over.forget S)
  f_open i j := by
    change IsOpenImmersion (pullback.fst (f i) (f j)).left
    exact hopen i j

def relativeMonoFamilyScheme : Scheme.{u} := (relativeMonoFamilyGlueData M U f).glued

def relativeMonoFamilyChart (i : J) : (U i).left ⟶ relativeMonoFamilyScheme M U f :=
  (relativeMonoFamilyGlueData M U f).ι i

instance relativeMonoFamilyChart_isOpenImmersion (i : J) :
    IsOpenImmersion (relativeMonoFamilyChart M U f i) :=
  Scheme.GlueData.ι_isOpenImmersion (relativeMonoFamilyGlueData M U f) i

def relativeMonoFamilyParameter : relativeMonoFamilyScheme M U f ⟶ M.left := by
  fapply Multicoequalizer.desc
  · exact fun i => (f i).left
  · rintro ⟨i, j⟩
    change (pullback.fst (f i) (f j)).left ≫ (f i).left =
      (((pullbackSymmetry (f i) (f j)).hom).left ≫ (pullback.fst (f j) (f i)).left) ≫ (f j).left
    have he : pullback.fst (f i) (f j) ≫ f i =
        (pullbackSymmetry (f i) (f j)).hom ≫ pullback.fst (f j) (f i) ≫ f j := by
      simp only [pullbackSymmetry_hom_comp_fst_assoc]
      exact pullback.condition
    exact congrArg Over.Hom.left he

theorem relativeMonoFamilyChart_parameter (i : J) :
    relativeMonoFamilyChart M U f i ≫ relativeMonoFamilyParameter M U f = (f i).left :=
  Multicoequalizer.π_desc _ _ _ _ _

theorem relativeMonoFamilyCharts_cover (x : relativeMonoFamilyScheme M U f) :
    ∃ i : J, ∃ y : (U i).left, relativeMonoFamilyChart M U f i y = x :=
  (relativeMonoFamilyGlueData M U f).ι_jointly_surjective x

theorem relativeMonoFamilyChart_intersection (i j : J) :
    IsPullback (pullback.fst (f i) (f j)).left (pullback.snd (f i) (f j)).left
      (relativeMonoFamilyChart M U f i) (relativeMonoFamilyChart M U f j) := by
  have hp := IsPullback.of_isLimit ((relativeMonoFamilyGlueData M U f).vPullbackConeIsLimit i j)
  have he : (pullbackSymmetry (f i) (f j)).hom ≫ pullback.fst (f j) (f i) =
      pullback.snd (f i) (f j) := pullbackSymmetry_hom_comp_fst _ _
  change IsPullback (pullback.fst (f i) (f j)).left
    (((pullbackSymmetry (f i) (f j)).hom ≫ pullback.fst (f j) (f i)).left) _ _ at hp
  rw [he] at hp
  exact hp

theorem relativeMonoFamilyParameter_injective : Function.Injective (relativeMonoFamilyParameter M U f) := by
  intro x y h
  obtain ⟨i, xi, rfl⟩ := relativeMonoFamilyCharts_cover M U f x
  obtain ⟨j, yj, rfl⟩ := relativeMonoFamilyCharts_cover M U f y
  have he : (f i).left xi = (f j).left yj := by
    rw [← relativeMonoFamilyChart_parameter M U f i, ← relativeMonoFamilyChart_parameter M U f j]
    exact h
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.exists_preimage_of_isPullback
    ((IsPullback.of_hasPullback (f i) (f j)).map (Over.forget S)) xi yj he
  rw [← hz₁, ← hz₂]
  exact congrArg (fun g : (pullback (f i) (f j)).left ⟶ relativeMonoFamilyScheme M U f => g z)
    (relativeMonoFamilyChart_intersection M U f i j).w

instance relativeMonoFamilyParameter_surjectiveOnStalks [hs : ∀ i, SurjectiveOnStalks (f i).left] :
    SurjectiveOnStalks (relativeMonoFamilyParameter M U f) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover
    (P := @SurjectiveOnStalks) (relativeMonoFamilyGlueData M U f).openCover).mpr
  intro i
  change J at i
  change SurjectiveOnStalks (relativeMonoFamilyChart M U f i ≫ relativeMonoFamilyParameter M U f)
  rw [relativeMonoFamilyChart_parameter]
  exact hs i

instance relativeMonoFamilyParameter_mono [∀ i, SurjectiveOnStalks (f i).left] :
    Mono (relativeMonoFamilyParameter M U f) :=
  SurjectiveOnStalks.mono_of_injective (relativeMonoFamilyParameter_injective M U f)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.MonoFamilyGluing
