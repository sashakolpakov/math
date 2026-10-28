import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage
import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SmoothWittFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PrincipalCovers
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OpenCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringObjectsSheafDetection

/-! # Frame Cover -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameCover.IntrinsicPadicFrameCover

noncomputable section

/-! An actual affine cover of the integral model gives a covering family of
its native bounded crystalline frames on the original special fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y

theorem exists_map (U : X.left.Opens) (hU : IsAffineOpen U)
    (T : IntegralComparison.BigCrystallineSite.Object p W (Ideal.span {(p : W)}) γ w)
    (t : Spec (CommRingCat.of (T.ring ⧸ T.ideal)) ⟶
      Spec (CommRingCat.of (AffineFrame.IntrinsicPadicAffineFrame.targetRing p X Y f U)))
    (ht : t ≫ ChartImage.IntrinsicPadicOpenFrame.chart p X Y f hp U hU = T.mapToX)
    (hn : (p : T.ring) ^ (n + 1) = 0) :
    Nonempty (T ⟶ (ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp U hU n).obj) := by
  let : Algebra ℤ_[p] (AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U) :=
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X U
  let : Algebra W (AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U) :=
    WittAlgebra.PadicWittAlgebra.algebra p (AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U)
  let : Algebra (ZMod p) (AffineFrame.IntrinsicPadicAffineFrame.targetRing p X Y f U) :=
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (ZMod p) Y (f ⁻¹ᵁ U)
  let := AffineFrame.IntrinsicPadicAffineFrame.source_smooth p X U hU
  let := AffineFrame.IntrinsicPadicAffineFrame.source_flat p X U hU
  exact IntegralComparison.Open.SmoothWittFrame.exists_map p (ZMod p)
    (AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U) (AffineFrame.IntrinsicPadicAffineFrame.targetRing p X Y f U)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction p X Y f U)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_surjective p X Y f hp U hU)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_kernel p X Y f hp U hU)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_base p X Y f hp U) Y
    (ChartImage.IntrinsicPadicOpenFrame.chart p X Y f hp U hU) (ChartImage.IntrinsicPadicOpenFrame.chart_over p X Y f hp U hU)
    n T t ht hn

variable {ι : Type} (U : ι → X.left.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (hcover : ∀ x : X.left, ∃ i, x ∈ U i)

include hcover in
omit [Smooth X.hom] in
theorem charts_cover (y : Y.left) : ∃ i, y ∈ Set.range (ChartImage.IntrinsicPadicOpenFrame.chart p X Y f hp (U i) (hU i)) := by
  obtain ⟨i, hi⟩ := hcover (f y)
  refine ⟨i, ?_⟩
  change y ∈ Set.range (ChartImage.IntrinsicPadicOpenFrame.special_affine p X Y f hp (U i) (hU i)).fromSpec
  rw [IsAffineOpen.range_fromSpec]
  exact hi

include hcover in
theorem covering (T : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) :
    IntegralComparison.CoveringObjectsSheafDetection.sieve (fun i => ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp (U i) (hU i) n) T ∈
      IntegralComparison.BoundedCrystalline.Site.topology w n T := by
  obtain ⟨s, hspan, hs⟩ := @IntegralComparison.Principal.OpenCover.finite_principal_refinement p W inferInstance
    (Ideal.span {(p : W)}) γ Y.left w T.obj ι
    (fun i => Spec (CommRingCat.of (AffineFrame.IntrinsicPadicAffineFrame.targetRing p X Y f (U i))))
    (fun i => ChartImage.IntrinsicPadicOpenFrame.chart p X Y f hp (U i) (hU i))
    (fun i => ChartImage.IntrinsicPadicOpenFrame.chart_open p X Y f hp (U i) (hU i))
    (charts_cover p X Y f hp U hU hcover)
  have hc : Sieve.generate (IntegralComparison.Bounded.PrincipalCovers.presieve T (fun r : s => r.val)) ∈ IntegralComparison.BoundedCrystalline.Site.topology w n T := by
    apply IntegralComparison.Bounded.PrincipalCovers.coveringSieve
    have he : Set.range (fun r : s => r.val) = (s : Set T.obj.ring) := by
      ext a
      exact ⟨fun ⟨b, hb⟩ => hb ▸ b.property, fun ha => ⟨⟨a, ha⟩, rfl⟩⟩
    rw [he]
    exact hspan
  apply (IntegralComparison.BoundedCrystalline.Site.topology w n).superset_covering _ hc
  apply (Sieve.generate_le_iff _ _).mpr
  intro V α hα
  cases hα with
  | mk r =>
    obtain ⟨i, hi⟩ := hs r.val r.property
    let L := IntegralComparison.Crystalline.Localization.object T.obj r.val
    let j := ChartImage.IntrinsicPadicOpenFrame.chart p X Y f hp (U i) (hU i)
    let t := IsOpenImmersion.lift j L.mapToX hi
    have ht : t ≫ j = L.mapToX := IsOpenImmersion.lift_fac j L.mapToX hi
    obtain ⟨a⟩ := exists_map p X Y f hp n (U i) (hU i) L t ht
      (IntegralComparison.Bounded.PrincipalCovers.object T r.val).property
    exact ⟨i, ⟨ObjectProperty.homMk a⟩⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameCover.IntrinsicPadicFrameCover
