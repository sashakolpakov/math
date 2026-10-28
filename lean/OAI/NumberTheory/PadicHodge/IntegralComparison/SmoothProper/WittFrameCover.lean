import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PrincipalCovers
import OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringObjectsSheafDetection

/-! # Witt Frame Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameCover

noncomputable section

/-! The fixed constructed flat Witt frames cover the entire original bounded crystalline site. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.StandardCover
open OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom] (n : ℕ)
  (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n)

theorem exists_cover :
    ∃ s : Finset U.obj.ring, Ideal.span (s : Set U.obj.ring) = ⊤ ∧
      Sieve.generate (Bounded.PrincipalCovers.presieve U (fun r : s => r.val)) ∈
        BoundedCrystalline.Site.topology (Witt.Crystalline.wittStructureMap p k X) n U ∧
      ∀ r ∈ s, ∃ i : StandardCover.Index k X, Nonempty (Bounded.PrincipalCovers.object U r ⟶ WittFrameFamily.Family.frame p k X n i) := by
  obtain ⟨s, hspan, hs⟩ := Principal.OpenCover.finite_principal_refinement U.obj
    (fun i => Spec (StandardCover.coordinateRing k X i)) (StandardCover.chartMap k X) (StandardCover.covers k X)
  refine ⟨s, hspan, ?_, ?_⟩
  · apply Bounded.PrincipalCovers.coveringSieve
    have he : Set.range (fun r : s => r.val) = (s : Set U.obj.ring) := by
      ext a
      exact ⟨fun ⟨b, hb⟩ => hb ▸ b.property, fun ha => ⟨⟨a, ha⟩, rfl⟩⟩
    rw [he]
    exact hspan
  · intro r hr
    obtain ⟨i, hi⟩ := hs r hr
    let V := Crystalline.Localization.object U.obj r
    let j : (Crystalline.Presentation.affineScheme k (StandardCover.coordinateRing k X i)).left ⟶ X.left := StandardCover.chartMap k X i
    let : IsOpenImmersion j := StandardCover.chartMap_open k X i
    let t := IsOpenImmersion.lift j V.mapToX hi
    have ht : t ≫ j = V.mapToX := IsOpenImmersion.lift_fac j V.mapToX hi
    obtain ⟨a⟩ := Open.SmoothWittFrame.exists_map p k (WittFrameFamily.Family.liftRing p k X i) (StandardCover.coordinateRing k X i)
      (WittFrameFamily.Family.reduction p k X i) (WittFrameFamily.Family.reduction_surjective p k X i) (WittFrameFamily.Family.reduction_kernel p k X i)
      (WittFrameFamily.Family.reduction_base p k X i) X j (StandardCover.chartMap_over k X i) n V t ht
      (Bounded.PrincipalCovers.object U r).property
    exact ⟨i, ⟨ObjectProperty.homMk a⟩⟩

theorem covering : CoveringObjectsSheafDetection.sieve (WittFrameFamily.Family.frame p k X n) U ∈
    BoundedCrystalline.Site.topology (Witt.Crystalline.wittStructureMap p k X) n U := by
  obtain ⟨s, _, hc, hs⟩ := exists_cover p k X n U
  apply (BoundedCrystalline.Site.topology (Witt.Crystalline.wittStructureMap p k X) n).superset_covering _ hc
  apply (Sieve.generate_le_iff _ _).mpr
  intro V α hα
  cases hα with
  | mk r => exact hs r.val r.property

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameCover
