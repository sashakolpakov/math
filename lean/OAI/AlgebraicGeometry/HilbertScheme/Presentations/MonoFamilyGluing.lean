import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MonoFamilyGlueData
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks

/-! # Mono Family Gluing -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MonoFamilyGluing

noncomputable section

/-! An actual scheme obtained by gluing a family of subobjects along their
open intersections in one ambient scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X : Scheme.{u}} {J : Type u} (Z : J → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
variable [∀ i, Mono (f i)] [hopen : ∀ i j, IsOpenImmersion (pullback.fst (f i) (f j))]

def schemeMonoFamilyGlueData : Scheme.GlueData where
  toGlueData := MonoFamilyGlueData.monoFamilyGlueData Z f
  f_open i j := hopen i j

def schemeMonoFamilyParameter : (schemeMonoFamilyGlueData Z f).glued ⟶ X := by
  fapply Multicoequalizer.desc
  · exact f
  · rintro ⟨i, j⟩
    change pullback.fst (f i) (f j) ≫ f i =
      ((pullbackSymmetry (f i) (f j)).hom ≫ pullback.fst (f j) (f i)) ≫ f j
    rw [pullbackSymmetry_hom_comp_fst]
    exact pullback.condition

@[reassoc]
theorem schemeMonoFamilyChart_parameter (i : J) :
    (schemeMonoFamilyGlueData Z f).ι i ≫ schemeMonoFamilyParameter Z f = f i :=
  Multicoequalizer.π_desc _ _ _ _ _

theorem schemeMonoFamilyChart_intersection (i j : J) :
    IsPullback (pullback.fst (f i) (f j)) (pullback.snd (f i) (f j))
      ((schemeMonoFamilyGlueData Z f).ι i) ((schemeMonoFamilyGlueData Z f).ι j) := by
  have hp := IsPullback.of_isLimit ((schemeMonoFamilyGlueData Z f).vPullbackConeIsLimit i j)
  change IsPullback (pullback.fst (f i) (f j))
    ((pullbackSymmetry (f i) (f j)).hom ≫ pullback.fst (f j) (f i)) _ _ at hp
  rwa [pullbackSymmetry_hom_comp_fst] at hp

theorem schemeMonoFamilyParameter_injective : Function.Injective (schemeMonoFamilyParameter Z f) := by
  intro x y h
  obtain ⟨i, xi, rfl⟩ := (schemeMonoFamilyGlueData Z f).ι_jointly_surjective x
  obtain ⟨j, yj, rfl⟩ := (schemeMonoFamilyGlueData Z f).ι_jointly_surjective y
  have he : f i xi = f j yj := by
    rw [← schemeMonoFamilyChart_parameter Z f i, ← schemeMonoFamilyChart_parameter Z f j]
    exact h
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback (f i) (f j)) xi yj he
  rw [← hz₁, ← hz₂]
  exact congrArg (fun g : pullback (f i) (f j) ⟶ (schemeMonoFamilyGlueData Z f).glued => g z)
    (schemeMonoFamilyChart_intersection Z f i j).w

instance schemeMonoFamilyParameter_surjectiveOnStalks [hs : ∀ i, SurjectiveOnStalks (f i)] :
    SurjectiveOnStalks (schemeMonoFamilyParameter Z f) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover
    (P := @SurjectiveOnStalks) (schemeMonoFamilyGlueData Z f).openCover).mpr
  intro i
  change J at i
  change SurjectiveOnStalks ((schemeMonoFamilyGlueData Z f).ι i ≫ schemeMonoFamilyParameter Z f)
  rw [schemeMonoFamilyChart_parameter]
  exact hs i

instance schemeMonoFamilyParameter_mono [∀ i, SurjectiveOnStalks (f i)] :
    Mono (schemeMonoFamilyParameter Z f) :=
  SurjectiveOnStalks.mono_of_injective (schemeMonoFamilyParameter_injective Z f)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MonoFamilyGluing
