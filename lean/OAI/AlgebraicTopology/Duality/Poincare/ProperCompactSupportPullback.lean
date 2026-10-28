import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph
import Mathlib.Topology.Maps.Proper.Basic

/-! # Proper Compact Support Pullback -/

namespace OAI.AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback

noncomputable section

/-!
# Proper pullback on actual compactly supported cohomology

A proper continuous map pulls a compact support back to a compact support.
The corresponding maps of genuine relative singular cochain kernels form a
cocone, hence induce pullback on the actual compact-support colimit complex.
The resulting map commutes with forgetting support and satisfies the usual
identity and composition laws. No duality or trace theorem is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

section CompactIndices

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Inverse image of actual compact subsets under a proper map. -/
def properCompactPreimage (f : X → Y) (hf : IsProperMap f) : Compacts Y →o Compacts X where
  toFun K := ⟨f ⁻¹' (K : Set Y), hf.isCompact_preimage K.isCompact⟩
  monotone' := fun _ _ h _ hx => h hx

@[simp]
theorem properCompactPreimage_coe (f : X → Y) (hf : IsProperMap f) (K : Compacts Y) :
    (properCompactPreimage f hf K : Set X) = f ⁻¹' (K : Set Y) := rfl

@[simp]
theorem properCompactPreimage_id (K : Compacts X) :
    properCompactPreimage (id : X → X) isProperMap_id K = K := by
  apply Compacts.ext
  rfl

@[simp]
theorem properCompactPreimage_comp (f : X → Y) (g : Y → Z)
    (hf : IsProperMap f) (hg : IsProperMap g) (K : Compacts Z) :
    properCompactPreimage (g ∘ f) (hg.comp hf) K =
      properCompactPreimage f hf (properCompactPreimage g hg K) := by
  apply Compacts.ext
  rfl

/-- The corresponding functor on the genuine compact-support index categories. -/
abbrev properCompactPreimageFunctor (f : X → Y) (hf : IsProperMap f) :
    Compacts Y ⥤ Compacts X :=
  (properCompactPreimage f hf).toFunctor

end CompactIndices

variable {R : Type} [Ring R] (M : ModuleCat.{0} R)
variable {X Y Z : TopCat.{0}}

/-- Genuine relative pullback at a compact support and its actual inverse image. -/
def compactSupportProperStagePullback (f : X ⟶ Y) (hf : IsProperMap f) (K : Compacts Y) :
    CompactSupportCohomology.compactSupportCochainStage M Y K ⟶
      CompactSupportCohomology.compactSupportCochainStage M X (properCompactPreimage f hf K) :=
  Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M f (fun _ hx => hx)

/-- On ordinary cochains the stage map is exactly ordinary singular pullback. -/
@[reassoc (attr := simp)]
theorem compactSupportProperStagePullback_inclusion (f : X ⟶ Y)
    (hf : IsProperMap f) (K : Compacts Y) :
    compactSupportProperStagePullback M f hf K ≫
        CompactSupportCohomology.compactSupportCochainStageInclusion M X (properCompactPreimage f hf K) =
      CompactSupportCohomology.compactSupportCochainStageInclusion M Y K ≫ Cohomology.Singular.Functor.singularPullback M f :=
  Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality M f (fun _ hx => hx)

/-- The genuine stage pullbacks commute with enlargement of the compact support. -/
@[reassoc]
theorem compactSupportProperStagePullback_naturality (f : X ⟶ Y)
    (hf : IsProperMap f) {K L : Compacts Y} (h : K ≤ L) :
    CompactSupportCohomology.compactSupportCochainMap M h ≫ compactSupportProperStagePullback M f hf L =
      compactSupportProperStagePullback M f hf K ≫
        CompactSupportCohomology.compactSupportCochainMap M ((properCompactPreimage f hf).monotone h) := by
  apply (cancel_mono
    (CompactSupportCohomology.compactSupportCochainStageInclusion M X (properCompactPreimage f hf L))).1
  simp only [Category.assoc, compactSupportProperStagePullback_inclusion,
    CompactSupportCohomology.compactSupportCochainMap_inclusion]
  exact CompactSupportCohomology.compactSupportCochainMap_inclusion_assoc M h _

/-- Proper pullback is an actual natural transformation of support diagrams. -/
def compactSupportProperDiagramMap (f : X ⟶ Y) (hf : IsProperMap f) :
    CompactSupportCohomology.compactSupportCochainDiagram M Y ⟶
      properCompactPreimageFunctor f hf ⋙ CompactSupportCohomology.compactSupportCochainDiagram M X where
  app K := compactSupportProperStagePullback M f hf K
  naturality _ _ h := compactSupportProperStagePullback_naturality M f hf (leOfHom h)

/-- Compose the actual stage pullbacks with the actual colimit insertions. -/
def compactSupportProperPullbackCocone (f : X ⟶ Y) (hf : IsProperMap f) :
    Cocone (CompactSupportCohomology.compactSupportCochainDiagram M Y) where
  pt := CompactSupportCohomology.compactSupportedCochains M X
  ι := {
    app := fun K => compactSupportProperStagePullback M f hf K ≫
      CompactSupportCohomology.compactSupportCochainι M X (properCompactPreimage f hf K)
    naturality := fun K L h => by
      change CompactSupportCohomology.compactSupportCochainMap M (leOfHom h) ≫
          (compactSupportProperStagePullback M f hf L ≫ _) = _ ≫ 𝟙 _
      rw [Category.comp_id, ← Category.assoc,
        compactSupportProperStagePullback_naturality, Category.assoc,
        CompactSupportCohomology.compactSupportCochainMap_ι] }

/-- Pullback on the actual compactly supported singular cochain complex. -/
def compactSupportedCochainProperPullback (f : X ⟶ Y) (hf : IsProperMap f) :
    CompactSupportCohomology.compactSupportedCochains M Y ⟶ CompactSupportCohomology.compactSupportedCochains M X :=
  colimit.desc (CompactSupportCohomology.compactSupportCochainDiagram M Y) (compactSupportProperPullbackCocone M f hf)

/-- The colimit pullback is the genuine relative pullback at every compact support. -/
@[reassoc (attr := simp)]
theorem compactSupportCochainι_properPullback (f : X ⟶ Y) (hf : IsProperMap f)
    (K : Compacts Y) :
    CompactSupportCohomology.compactSupportCochainι M Y K ≫ compactSupportedCochainProperPullback M f hf =
      compactSupportProperStagePullback M f hf K ≫
        CompactSupportCohomology.compactSupportCochainι M X (properCompactPreimage f hf K) :=
  colimit.ι_desc (compactSupportProperPullbackCocone M f hf) K

/-- Forgetting compact support gives exactly ordinary singular pullback. -/
@[reassoc (attr := simp)]
theorem compactSupportedCochainProperPullback_forget (f : X ⟶ Y) (hf : IsProperMap f) :
    compactSupportedCochainProperPullback M f hf ≫ CompactSupportCohomology.compactSupportedCochainForget M X =
      CompactSupportCohomology.compactSupportedCochainForget M Y ≫ Cohomology.Singular.Functor.singularPullback M f := by
  apply colimit.hom_ext
  intro K
  rw [compactSupportCochainι_properPullback_assoc, CompactSupportCohomology.compactSupportCochainι_forget,
    CompactSupportCohomology.compactSupportCochainι_forget_assoc, compactSupportProperStagePullback_inclusion]

/-- The identity proper map acts identically on the genuine compact-support complex. -/
@[simp]
theorem compactSupportedCochainProperPullback_id (X : TopCat.{0}) :
    compactSupportedCochainProperPullback M (𝟙 X) isProperMap_id =
      𝟙 (CompactSupportCohomology.compactSupportedCochains M X) := by
  apply (cancel_mono (CompactSupportCohomology.compactSupportedCochainForget M X)).1
  rw [compactSupportedCochainProperPullback_forget, Cohomology.Singular.Functor.singularPullback_id,
    Category.comp_id, Category.id_comp]

/-- Proper pullbacks compose in the contravariant order. -/
theorem compactSupportedCochainProperPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsProperMap f) (hg : IsProperMap g) :
    compactSupportedCochainProperPullback M (f ≫ g) (hg.comp hf) =
      compactSupportedCochainProperPullback M g hg ≫
        compactSupportedCochainProperPullback M f hf := by
  apply (cancel_mono (CompactSupportCohomology.compactSupportedCochainForget M X)).1
  rw [compactSupportedCochainProperPullback_forget, Category.assoc,
    compactSupportedCochainProperPullback_forget, ← Category.assoc,
    compactSupportedCochainProperPullback_forget, Category.assoc, Cohomology.Singular.Functor.singularPullback_comp]

/-- This extends the already constructed genuine homeomorphism pullback. -/
theorem compactSupportedCochainProperPullback_homeomorph (e : X ≃ₜ Y) :
    compactSupportedCochainProperPullback M (TopCat.isoOfHomeo e).hom e.isProperMap =
      (CompactSupportHomeomorph.compactSupportedCochainsHomeomorphIso M e).hom := by
  apply (cancel_mono (CompactSupportCohomology.compactSupportedCochainForget M X)).1
  rw [compactSupportedCochainProperPullback_forget, CompactSupportHomeomorph.compactSupportedCochainsHomeomorphIso_forget]

/-- The actual relative-cohomology pullback at one compact support. -/
abbrev compactSupportProperStageCohomologyPullback (f : X ⟶ Y) (hf : IsProperMap f)
    (K : Compacts Y) (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology M Y (K : Set Y)ᶜ n ⟶
      Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X (properCompactPreimage f hf K : Set X)ᶜ n :=
  HomologicalComplex.homologyMap (compactSupportProperStagePullback M f hf K) n

/-- Proper pullback on actual compactly supported singular cohomology. -/
abbrev compactSupportedCohomologyProperPullback (f : X ⟶ Y) (hf : IsProperMap f) (n : ℕ) :
    CompactSupportCohomology.compactSupportedCohomology M Y n ⟶ CompactSupportCohomology.compactSupportedCohomology M X n :=
  HomologicalComplex.homologyMap (compactSupportedCochainProperPullback M f hf) n

/-- Proper cohomology pullback is induced by the actual stage pullbacks. -/
@[reassoc (attr := simp)]
theorem compactSupportCohomologyι_properPullback (f : X ⟶ Y) (hf : IsProperMap f)
    (K : Compacts Y) (n : ℕ) :
    CompactSupportCohomology.compactSupportCohomologyι M Y K n ≫ compactSupportedCohomologyProperPullback M f hf n =
      compactSupportProperStageCohomologyPullback M f hf K n ≫
        CompactSupportCohomology.compactSupportCohomologyι M X (properCompactPreimage f hf K) n := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    compactSupportCochainι_properPullback]

/-- Forgetting compact support commutes with actual proper cohomology pullback. -/
@[reassoc (attr := simp)]
theorem compactSupportedCohomologyProperPullback_forget (f : X ⟶ Y)
    (hf : IsProperMap f) (n : ℕ) :
    compactSupportedCohomologyProperPullback M f hf n ≫
        CompactSupportCohomology.compactSupportedCohomologyForget M X n =
      CompactSupportCohomology.compactSupportedCohomologyForget M Y n ≫ Cohomology.Singular.Functor.singularCohomologyPullback M f n := by
  change HomologicalComplex.homologyMap (compactSupportedCochainProperPullback M f hf) n ≫
      HomologicalComplex.homologyMap (CompactSupportCohomology.compactSupportedCochainForget M X) n =
    HomologicalComplex.homologyMap (CompactSupportCohomology.compactSupportedCochainForget M Y) n ≫
      HomologicalComplex.homologyMap (Cohomology.Singular.Functor.singularPullback M f) n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    compactSupportedCochainProperPullback_forget]

@[simp]
theorem compactSupportedCohomologyProperPullback_id (X : TopCat.{0}) (n : ℕ) :
    compactSupportedCohomologyProperPullback M (𝟙 X) isProperMap_id n =
      𝟙 (CompactSupportCohomology.compactSupportedCohomology M X n) := by
  rw [compactSupportedCohomologyProperPullback, compactSupportedCochainProperPullback_id,
    HomologicalComplex.homologyMap_id]

/-- The induced cohomology maps satisfy the actual contravariant composition law. -/
theorem compactSupportedCohomologyProperPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsProperMap f) (hg : IsProperMap g) (n : ℕ) :
    compactSupportedCohomologyProperPullback M (f ≫ g) (hg.comp hf) n =
      compactSupportedCohomologyProperPullback M g hg n ≫
        compactSupportedCohomologyProperPullback M f hf n := by
  rw [compactSupportedCohomologyProperPullback, compactSupportedCochainProperPullback_comp,
    HomologicalComplex.homologyMap_comp]

/-- The induced cohomology pullback agrees with genuine homeomorphism transport. -/
theorem compactSupportedCohomologyProperPullback_homeomorph (e : X ≃ₜ Y) (n : ℕ) :
    compactSupportedCohomologyProperPullback M (TopCat.isoOfHomeo e).hom e.isProperMap n =
      (CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso M e n).hom := by
  rw [compactSupportedCohomologyProperPullback, compactSupportedCochainProperPullback_homeomorph]
  rfl

end

end OAI.AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback
