import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameAlgebras
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PrincipalCovers
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OpenCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringObjectsSheafDetection

/-! # Frame Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameCover

noncomputable section

/-! An actual affine cover of a smooth finite-Witt-level model covers
the entire original bounded crystalline site of its special fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of k))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

local notation "W" => WittVector p k
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k

theorem exists_map (U : X.left.Opens) (hU : IsAffineOpen U)
    (T : BigCrystallineSite.Object p W (Ideal.span {(p : W)}) γ w)
    (t : Spec (CommRingCat.of (T.ring ⧸ T.ideal)) ⟶
      Spec (Truncated.AffineModelFrame.targetRing p k n X Y f U))
    (ht : t ≫ Truncated.AffineModelFrame.chart p k n X Y f hp U hU = T.mapToX)
    (hn : (p : T.ring) ^ (n + 1) = 0) :
    Nonempty (T ⟶ (Truncated.AffineModelFrame.frame p k n X Y f hp U hU).obj) := by
  let A := Truncated.AffineModelFrame.sourceRing p k n X U
  let C := Truncated.AffineModelFrame.targetRing p k n X Y f U
  let : Algebra S A := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X U
  let : Algebra k C := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra k Y (f ⁻¹ᵁ U)
  let := Truncated.AffineModelFrame.source_smooth p k n X U hU
  let j := Truncated.AffineModelFrame.chart p k n X Y f hp U hU
  let hj := Truncated.AffineModelFrame.chart_over p k n X Y f hp U hU
  let V := Crystalline.OpenPresentation.affineObject p k C Y j hj T t ht
  obtain ⟨a⟩ := Truncated.FrameAlgebras.SmoothLifting.exists_morphism p k n A C
    (Truncated.AffineModelFrame.reduction p k n X Y f U)
    (Truncated.AffineModelFrame.reduction_base p k n X Y f hp U hU)
    ⟨V, hn⟩ (Truncated.AffineModelFrame.reduction_surjective p k n X Y f hp U hU)
    (Truncated.AffineModelFrame.reduction_kernel p k n X Y f hp U hU)
  refine ⟨{ ringMap := a.hom.ringMap, overBase := a.hom.overBase, overX := ?_ }⟩
  change BigCrystallineSite.Object.closed.map a.hom ≫
    ((Truncated.AffineModelFrame.localFrame p k n X Y f hp U hU).obj.mapToX ≫ j) = T.mapToX
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ j) a.hom.overX).trans ht)

variable {ι : Type} (U : ι → X.left.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (hcover : ∀ x : X.left, ∃ i, x ∈ U i)

omit [Smooth X.hom] in
include hcover in
theorem charts_cover (y : Y.left) :
    ∃ i, y ∈ Set.range (Truncated.AffineModelFrame.chart p k n X Y f hp (U i) (hU i)) := by
  obtain ⟨i, hi⟩ := hcover (f y)
  refine ⟨i, ?_⟩
  change y ∈ Set.range (Truncated.AffineModelFrame.residue_affine p k n X Y f hp (U i) (hU i)).fromSpec
  rw [IsAffineOpen.range_fromSpec]
  exact hi

include hcover in
theorem covering (T : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) :
    CoveringObjectsSheafDetection.sieve
      (fun i => Truncated.AffineModelFrame.frame p k n X Y f hp (U i) (hU i)) T ∈ BoundedCrystalline.Site.topology w n T := by
  obtain ⟨s, hspan, hs⟩ := @Principal.OpenCover.finite_principal_refinement p W inferInstance
    (Ideal.span {(p : W)}) γ Y.left w T.obj ι
    (fun i => Spec (Truncated.AffineModelFrame.targetRing p k n X Y f (U i)))
    (fun i => Truncated.AffineModelFrame.chart p k n X Y f hp (U i) (hU i))
    (fun i => Truncated.AffineModelFrame.chart_open p k n X Y f hp (U i) (hU i))
    (charts_cover p k n X Y f hp U hU hcover)
  have hc : Sieve.generate (Bounded.PrincipalCovers.presieve T (fun r : s => r.val)) ∈ BoundedCrystalline.Site.topology w n T := by
    apply Bounded.PrincipalCovers.coveringSieve
    have he : Set.range (fun r : s => r.val) = (s : Set T.obj.ring) := by
      ext a
      exact ⟨fun ⟨b, hb⟩ => hb ▸ b.property, fun ha => ⟨⟨a, ha⟩, rfl⟩⟩
    rw [he]
    exact hspan
  apply (BoundedCrystalline.Site.topology w n).superset_covering _ hc
  apply (Sieve.generate_le_iff _ _).mpr
  intro V α hα
  cases hα with
  | mk r =>
    obtain ⟨i, hi⟩ := hs r.val r.property
    let L := Crystalline.Localization.object T.obj r.val
    let j := Truncated.AffineModelFrame.chart p k n X Y f hp (U i) (hU i)
    let t := IsOpenImmersion.lift j L.mapToX hi
    have ht : t ≫ j = L.mapToX := IsOpenImmersion.lift_fac j L.mapToX hi
    obtain ⟨a⟩ := exists_map p k n X Y f hp (U i) (hU i) L t ht
      (Bounded.PrincipalCovers.object T r.val).property
    exact ⟨i, ⟨ObjectProperty.homMk a⟩⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameCover
