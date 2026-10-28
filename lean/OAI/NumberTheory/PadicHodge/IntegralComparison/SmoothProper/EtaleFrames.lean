import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.EtaleCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFrameProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.EtaleZeroFrameProduct

/-! # Etale Frames -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.EtaleFrames

noncomputable section

/-!
# IntegralComparison: finitely many original étale zero frames cover the entire zeroth-level crystalline site
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.EtaleCover
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

def frame (i : EtaleCover.Index k X) : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) 0 :=
  ZeroLevel.OpenFrame.boundedFrame p k (EtaleCover.coordinateRing k X i) X (EtaleCover.chartMap k X i) (EtaleCover.chartMap_over k X i)

theorem exists_cover (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) 0) :
    ∃ s : Finset U.obj.ring, Ideal.span (s : Set U.obj.ring) = ⊤ ∧
      Sieve.generate (Bounded.PrincipalCovers.presieve U (fun r : s => r.val)) ∈
        BoundedCrystalline.Site.topology (Witt.Crystalline.wittStructureMap p k X) 0 U ∧
      ∀ r ∈ s, ∃ i : EtaleCover.Index k X, Nonempty (Bounded.PrincipalCovers.object U r ⟶ frame p k X i) := by
  obtain ⟨s, hspan, hs⟩ := Principal.OpenCover.finite_principal_refinement U.obj
    (fun i => Spec (EtaleCover.coordinateRing k X i)) (EtaleCover.chartMap k X) (EtaleCover.covers k X)
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
    let j : (Crystalline.Presentation.affineScheme k (EtaleCover.coordinateRing k X i)).left ⟶ X.left := EtaleCover.chartMap k X i
    let : IsOpenImmersion j := EtaleCover.chartMap_open k X i
    let : Algebra.Smooth k (EtaleCover.coordinateRing k X i) :=
      BoundedEtale.ZeroFrameProduct.smooth k (EtaleCover.coordinateRing k X i) (EtaleCover.coordinateIndex k X i)
    let t := IsOpenImmersion.lift j V.mapToX hi
    have ht : t ≫ j = V.mapToX := IsOpenImmersion.lift_fac j V.mapToX hi
    have hU : (p : U.obj.ring) = 0 := (pow_one (p : U.obj.ring)).symm.trans U.property
    have hV : (p : V.ring) = 0 := by
      simpa only [map_natCast, map_zero] using
        congrArg (algebraMap U.obj.ring (Crystalline.Localization.Ring U.obj r)) hU
    obtain ⟨a⟩ := ZeroLevel.OpenFrame.exists_map p k (EtaleCover.coordinateRing k X i) X j
      (EtaleCover.chartMap_over k X i) V t ht hV
    exact ⟨i, ⟨ObjectProperty.homMk a⟩⟩

variable (i : EtaleCover.Index k X)
  (U : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X))
  (α : U ⟶ (frame p k X i).obj)

def productCone : BinaryFan U (frame p k X i).obj := by
  exact @Open.EtaleZeroFrameProduct.cone p inferInstance k (EtaleCover.coordinateRing k X i) (EtaleCover.coordinateIndex k X i)
    inferInstance inferInstance inferInstance (EtaleCover.coordinateAlgebra k X i) (EtaleCover.polynomialAlgebra k X i)
    (EtaleCover.coordinateTower k X i) (EtaleCover.coordinateEtale k X i) X
    (EtaleCover.chartMap k X i) (EtaleCover.chartMap_over k X i) U α

def isProduct : IsLimit (productCone p k X i U α) := by
  exact @Open.EtaleZeroFrameProduct.isProduct p inferInstance k (EtaleCover.coordinateRing k X i) (EtaleCover.coordinateIndex k X i)
    inferInstance inferInstance inferInstance (EtaleCover.coordinateAlgebra k X i) (EtaleCover.polynomialAlgebra k X i)
    (EtaleCover.coordinateTower k X i) (EtaleCover.coordinateEtale k X i) X
    (EtaleCover.chartMap k X i) (EtaleCover.chartMap_open k X i) (EtaleCover.chartMap_over k X i) U α

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.EtaleFrames
