import OAI.NumberTheory.PadicHodge.IntegralComparison.ProperCrystallineFrames
import OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.OpenFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PrincipalCovers
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Zero Frames -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.ZeroFrames

noncomputable section

/-!
# IntegralComparison: a fixed finite family of smooth zero frames covers the original bounded site
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.ProperAffineCover
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProperCrystallineFrames OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

instance coordinate_smooth (i : (ProperAffineCover.cover X.hom).I₀) : Algebra.Smooth k (ProperAffineCover.coordinateRing X.hom i) := by
  have h : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (ProperAffineCover.coordinateRing X.hom i)))) := by
    rw [← ProperAffineCover.chartMap_over X.hom i]
    infer_instance
  exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp h)

theorem exists_cover (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) 0) :
    ∃ s : Finset U.obj.ring, Ideal.span (s : Set U.obj.ring) = ⊤ ∧
      Sieve.generate (Bounded.PrincipalCovers.presieve U (fun r : s => r.val)) ∈
        BoundedCrystalline.Site.topology (Witt.Crystalline.wittStructureMap p k X) 0 U ∧
      ∀ r ∈ s, ∃ i : (ProperAffineCover.cover X.hom).I₀,
        Nonempty (Bounded.PrincipalCovers.object U r ⟶
          ZeroLevel.OpenFrame.boundedFrame p k (ProperAffineCover.coordinateRing X.hom i) X
            (ProperCrystallineFrames.affineChartMap k X i) (ProperCrystallineFrames.affineChartMap_over k X i)) := by
  have hcover : ∀ z : X.left, ∃ i, z ∈ Set.range (ProperAffineCover.chartMap X.hom i) := by
    intro z
    have hz : z ∈ (⨆ i, (ProperAffineCover.chartMap X.hom i).opensRange : X.left.Opens) := by
      rw [ProperAffineCover.chartMaps_cover]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hz
  obtain ⟨s, hspan, hs⟩ := Principal.OpenCover.finite_principal_refinement U.obj
    (fun i => Spec (ProperAffineCover.coordinateRing X.hom i)) (ProperAffineCover.chartMap X.hom) hcover
  refine ⟨s, hspan, ?_, ?_⟩
  · apply Bounded.PrincipalCovers.coveringSieve
    have he : Set.range (fun r : s => r.val) = (s : Set U.obj.ring) := by
      ext a
      constructor
      · rintro ⟨b, rfl⟩
        exact b.property
      · intro ha
        exact ⟨⟨a, ha⟩, rfl⟩
    rw [he]
    exact hspan
  · intro r hr
    obtain ⟨i, hi⟩ := hs r hr
    let V := Crystalline.Localization.object U.obj r
    let j : (Crystalline.Presentation.affineScheme k (ProperAffineCover.coordinateRing X.hom i)).left ⟶ X.left := ProperCrystallineFrames.affineChartMap k X i
    let : IsOpenImmersion j := ProperCrystallineFrames.affineChartMap_open k X i
    let t := IsOpenImmersion.lift j V.mapToX hi
    have ht : t ≫ j = V.mapToX := IsOpenImmersion.lift_fac j V.mapToX hi
    have hU : (p : U.obj.ring) = 0 := (pow_one (p : U.obj.ring)).symm.trans U.property
    have hV : (p : V.ring) = 0 := by
      simpa only [map_natCast, map_zero] using
        congrArg (algebraMap U.obj.ring (Crystalline.Localization.Ring U.obj r)) hU
    obtain ⟨a⟩ := ZeroLevel.OpenFrame.exists_map p k (ProperAffineCover.coordinateRing X.hom i) X j
      (ProperCrystallineFrames.affineChartMap_over k X i) V t ht hV
    exact ⟨i, ⟨ObjectProperty.homMk a⟩⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.ZeroFrames
