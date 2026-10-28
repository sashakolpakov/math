import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.MorphismNeighborhoods
import OAI.AlgebraicGeometry.Divisors.LineBundles.Section.OpenRestriction

/-! # Action Charts -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ActionCharts

noncomputable section

/-! Actual simultaneous affine charts for a finite pointed action.
All restricted maps and their section and base equations are constructed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

structure SectionMorphismChart {X Y : Scheme.{0}} (p : Y ⟶ X) (s : X ⟶ Y)
    {ι : Type} (f : ι → (Y ⟶ Y)) where
  U : Y.Opens
  W : Y.Opens
  V : X.Opens
  affineU : IsAffineOpen U
  affineW : IsAffineOpen W
  affineV : IsAffineOpen V
  sectionW : V ≤ s ⁻¹ᵁ W
  inclusion : W ≤ U
  overU : U ≤ p ⁻¹ᵁ V
  action : ∀ i, W ≤ f i ⁻¹ᵁ U

theorem exists_sectionMorphismChart {X Y : Scheme.{0}} (p : Y ⟶ X) (s : X ⟶ Y)
    (hs : s ≫ p = 𝟙 X) {ι : Type} [Finite ι] (f : ι → (Y ⟶ Y))
    (hf : ∀ i, f i ≫ p = p) (he : ∀ i, s ≫ f i = s) (x : X) :
    ∃ C : SectionMorphismChart p s f, x ∈ C.V := by
  obtain ⟨U, W, V, hU, hW, hV, hx, hsW, hWU, hUV, hact⟩ :=
    MorphismNeighborhoods.section_exists_affine_morphism_neighborhoods p s hs f hf he x
  exact ⟨⟨U, W, V, hU, hW, hV, hsW, hWU, hUV, hact⟩, hx⟩

namespace SectionMorphismChart
open OAI.AlgebraicGeometry.Divisors.LineBundles.Section.OpenRestriction.BundleCycles

variable {X Y : Scheme.{0}} {p : Y ⟶ X} {s : X ⟶ Y} {ι : Type} {f : ι → (Y ⟶ Y)}
  (C : SectionMorphismChart p s f)

instance : IsAffine C.U.toScheme := C.affineU
instance : IsAffine C.W.toScheme := C.affineW
instance : IsAffine C.V.toScheme := C.affineV

theorem sectionU : C.V ≤ s ⁻¹ᵁ C.U := fun _ hx => C.inclusion (C.sectionW hx)

theorem overW : C.W ≤ p ⁻¹ᵁ C.V := le_trans C.inclusion C.overU

def targetProjection : C.U.toScheme ⟶ C.V.toScheme := Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenProjection p C.U C.V C.overU
def sourceProjection : C.W.toScheme ⟶ C.V.toScheme := Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenProjection p C.W C.V C.overW
def targetSection : C.V.toScheme ⟶ C.U.toScheme := Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenMap s C.U C.V C.sectionU
def sourceSection : C.V.toScheme ⟶ C.W.toScheme := Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenMap s C.W C.V C.sectionW

instance [Smooth p] : Smooth C.targetProjection := Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenProjection_smooth p C.U C.V C.overU
instance [Smooth p] : Smooth C.sourceProjection := Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenProjection_smooth p C.W C.V C.overW

theorem target_retraction (hs : s ≫ p = 𝟙 X) :
    C.targetSection ≫ C.targetProjection = 𝟙 C.V.toScheme :=
  Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpen_retraction p s hs C.U C.V C.sectionU C.overU

theorem source_retraction (hs : s ≫ p = 𝟙 X) :
    C.sourceSection ≫ C.sourceProjection = 𝟙 C.V.toScheme :=
  Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpen_retraction p s hs C.W C.V C.sectionW C.overW

def inclusionMap : C.W.toScheme ⟶ C.U.toScheme := Y.homOfLE C.inclusion

instance : IsOpenImmersion C.inclusionMap := inferInstanceAs (IsOpenImmersion (Y.homOfLE C.inclusion))

def actionMap (i : ι) : C.W.toScheme ⟶ C.U.toScheme :=
  Y.homOfLE (C.action i) ≫ morphismRestrict (f i) C.U

theorem actionMap_ι (i : ι) : C.actionMap i ≫ C.U.ι = C.W.ι ≫ f i := by
  dsimp only [SectionMorphismChart.actionMap]
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]

theorem inclusion_over : C.inclusionMap ≫ C.targetProjection = C.sourceProjection := by
  apply (cancel_mono C.V.ι).mp
  change (Y.homOfLE C.inclusion ≫ Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenProjection p C.U C.V C.overU) ≫ C.V.ι =
    Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenProjection p C.W C.V C.overW ≫ C.V.ι
  rw [Category.assoc, Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenProjection_ι, Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenProjection_ι,
    ← Category.assoc, Scheme.homOfLE_ι]

theorem inclusion_section : C.sourceSection ≫ C.inclusionMap = C.targetSection := by
  apply (cancel_mono C.U.ι).mp
  change (Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenMap s C.W C.V C.sectionW ≫ Y.homOfLE C.inclusion) ≫ C.U.ι =
    Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenMap s C.U C.V C.sectionU ≫ C.U.ι
  rw [Category.assoc, Scheme.homOfLE_ι, Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenMap_ι, Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenMap_ι]

theorem actionMap_over (hf : ∀ i, f i ≫ p = p) (i : ι) :
    C.actionMap i ≫ C.targetProjection = C.sourceProjection := by
  apply (cancel_mono C.V.ι).mp
  change (C.actionMap i ≫ Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenProjection p C.U C.V C.overU) ≫ C.V.ι =
    Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenProjection p C.W C.V C.overW ≫ C.V.ι
  rw [Category.assoc, Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenProjection_ι, Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenProjection_ι,
    ← Category.assoc, actionMap_ι, Category.assoc, hf i]

theorem actionMap_section (he : ∀ i, s ≫ f i = s) (i : ι) :
    C.sourceSection ≫ C.actionMap i = C.targetSection := by
  apply (cancel_mono C.U.ι).mp
  change (Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenMap s C.W C.V C.sectionW ≫ C.actionMap i) ≫ C.U.ι =
    Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenMap s C.U C.V C.sectionU ≫ C.U.ι
  rw [Category.assoc, actionMap_ι, ← Category.assoc, Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenMap_ι,
    Category.assoc, he i, Divisors.LineBundles.Section.OpenRestriction.BundleCycles.sectionOpenMap_ι]

end SectionMorphismChart

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ActionCharts
