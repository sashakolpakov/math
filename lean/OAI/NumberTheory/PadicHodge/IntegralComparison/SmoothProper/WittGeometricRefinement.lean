import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalizationLift

/-! # Witt Geometric Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittGeometricRefinement

noncomputable section

/-! Every genuine morphism between smooth proper special fibres admits
an actual bounded Witt-frame refinement. The refined source objects are
principal opens in the constructed source frames, and carry actual
crystalline arrows to the target frames. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.StandardCover
  BoundedCrystalline.Site

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X Y : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  [IsProper Y.hom] [Smooth Y.hom] (g : X ⟶ Y) (n : ℕ)

local notation "WX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "WY" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "PIdeal" => Ideal.span {(p : WittVector p k)}
local notation "DP" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k

omit [Fintype k] [CharP k p] [IsProper X.hom] [Smooth X.hom] [IsProper Y.hom] [Smooth Y.hom] in
theorem over_witt : g.left ≫ WY = WX := by
  change g.left ≫ (Y.hom ≫ _) = X.hom ≫ _
  rw [← Category.assoc, g.w]

abbrev postcompose := BoundedOpen.Equivalence.postcompose
  (p := p) (J := PIdeal) (δ := DP) g.left (over_witt p k X Y g) n

def elements (i : StandardCover.Index k X) : Finset ((WittFrameFamily.Family.frame p k X n i).obj.ring) :=
  (WittFrameCover.exists_cover p k Y n ((postcompose p k X Y g n).obj (WittFrameFamily.Family.frame p k X n i))).choose

theorem elements_span (i : StandardCover.Index k X) :
    Ideal.span (elements p k X Y g n i : Set ((WittFrameFamily.Family.frame p k X n i).obj.ring)) = ⊤ :=
  (WittFrameCover.exists_cover p k Y n
    ((postcompose p k X Y g n).obj (WittFrameFamily.Family.frame p k X n i))).choose_spec.1

abbrev RefinedIndex := Σ i : StandardCover.Index k X, (elements p k X Y g n i)

def source (i : RefinedIndex p k X Y g n) : BoundedCrystalline.Site.Objects (p := p) (J := PIdeal) (δ := DP) WX n :=
  Bounded.PrincipalCovers.object (WittFrameFamily.Family.frame p k X n i.1) i.2.val

def sourceMap (i : RefinedIndex p k X Y g n) : source p k X Y g n i ⟶ WittFrameFamily.Family.frame p k X n i.1 :=
  Bounded.PrincipalCovers.hom (WittFrameFamily.Family.frame p k X n i.1) i.2.val

theorem target_exists (i : RefinedIndex p k X Y g n) :
    ∃ j : StandardCover.Index k Y, Nonempty ((postcompose p k X Y g n).obj (source p k X Y g n i) ⟶ WittFrameFamily.Family.frame p k Y n j) := by
  obtain ⟨j, ⟨α⟩⟩ := (WittFrameCover.exists_cover p k Y n
    ((postcompose p k X Y g n).obj (WittFrameFamily.Family.frame p k X n i.1))).choose_spec.2.2 i.2.val i.2.property
  let β := ((postcompose p k X Y g n).map (sourceMap p k X Y g n i)).hom
  have hu : IsUnit (β.ringMap i.2.val) :=
    IsLocalization.Away.algebraMap_isUnit
      (S := Crystalline.Localization.Ring (WittFrameFamily.Family.frame p k X n i.1).obj i.2.val) i.2.val
  exact ⟨j, ⟨ObjectProperty.homMk
    (Crystalline.LocalizationLift.liftHom β i.2.val hu) ≫ α⟩⟩

def targetIndex (i : RefinedIndex p k X Y g n) : StandardCover.Index k Y :=
  (target_exists p k X Y g n i).choose

def targetMap (i : RefinedIndex p k X Y g n) :
    (postcompose p k X Y g n).obj (source p k X Y g n i) ⟶
      WittFrameFamily.Family.frame p k Y n (targetIndex p k X Y g n i) :=
  Classical.choice (target_exists p k X Y g n i).choose_spec

/-- The refined family still covers the whole original bounded source site. -/
theorem covering (U : BoundedCrystalline.Site.Objects (p := p) (J := PIdeal) (δ := DP) WX n) :
    CoveringObjectsSheafDetection.sieve (source p k X Y g n) U ∈ BoundedCrystalline.Site.topology WX n U := by
  have hf (i : StandardCover.Index k X) :
      CoveringObjectsSheafDetection.sieve (source p k X Y g n) (WittFrameFamily.Family.frame p k X n i) ∈
        BoundedCrystalline.Site.topology WX n (WittFrameFamily.Family.frame p k X n i) := by
    let s := elements p k X Y g n i
    have he : Set.range (fun r : s => r.val) = (s : Set ((WittFrameFamily.Family.frame p k X n i).obj.ring)) := by
      ext r
      exact ⟨fun ⟨a, ha⟩ => ha ▸ a.property, fun hr => ⟨⟨r, hr⟩, rfl⟩⟩
    have hc := Bounded.PrincipalCovers.coveringSieve (WittFrameFamily.Family.frame p k X n i) (fun r : s => r.val)
      (by rw [he]; exact elements_span p k X Y g n i)
    apply (BoundedCrystalline.Site.topology WX n).superset_covering _ hc
    apply (Sieve.generate_le_iff _ _).mpr
    intro V α hα
    cases hα with
    | mk r => exact ⟨⟨i, r⟩, ⟨𝟙 _⟩⟩
  apply (BoundedCrystalline.Site.topology WX n).transitive (WittFrameCover.covering p k X n U)
  rintro V α ⟨i, ⟨β⟩⟩
  exact (BoundedCrystalline.Site.topology WX n).pullback_stable β (hf i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittGeometricRefinement
