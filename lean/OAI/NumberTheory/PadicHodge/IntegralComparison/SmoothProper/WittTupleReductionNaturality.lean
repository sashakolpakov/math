import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittTupleReductionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.ResolutionFaceMaps

/-! # Witt Tuple Reduction Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittTupleReductionNaturality

noncomputable section

/-! Actual Witt tuple quotient maps commute with all Čech restriction maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.StandardCover OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittTupleReduction

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

local instance separated : IsSeparated (Witt.Crystalline.wittStructureMap p k X) := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

theorem projection_comp (n a b : ℕ) (θ : Fin (b + 1) → Fin (a + 1))
    (t : Fin (a + 1) → StandardCover.Index k X) (c : Fin (b + 1)) :
    (Presentation.ResolutionFaceMaps.productMap.{u + 1, u} (WittFrameFamily.Family.frame p k X n) θ t).hom ≫
      (Pi.π (fun c => WittFrameFamily.Family.frame p k X n ((t ∘ θ) c)) c).hom =
        (Pi.π (fun c => WittFrameFamily.Family.frame p k X n (t c)) (θ c)).hom := by
  let L := BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n
  exact (L.map_comp _ _).symm.trans (congrArg L.map (Pi.lift_comp_π (fun c => Pi.π (fun d => WittFrameFamily.Family.frame p k X n (t d)) (θ c)) c))

theorem natural (n m : ℕ) (hnm : n ≤ m) (a b : ℕ) (θ : Fin (b + 1) → Fin (a + 1))
    (t : Fin (a + 1) → StandardCover.Index k X) :
    WittTupleReduction.morphism p k X n m hnm a t ≫ (Presentation.ResolutionFaceMaps.productMap.{u + 1, u} (WittFrameFamily.Family.frame p k X m) θ t).hom =
      (Presentation.ResolutionFaceMaps.productMap.{u + 1, u} (WittFrameFamily.Family.frame p k X n) θ t).hom ≫ WittTupleReduction.morphism p k X n m hnm b (t ∘ θ) := by
  let L := BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) m
  let c := limit.cone (Discrete.functor (fun c : Fin (b + 1) => WittFrameFamily.Family.frame p k X m ((t ∘ θ) c)))
  let hc : IsLimit (L.mapCone c) := isLimitOfPreserves L (limit.isLimit _)
  apply hc.hom_ext
  rintro ⟨d⟩
  have hl := (Category.assoc _ _ _).trans
    ((congrArg (fun f => WittTupleReduction.morphism p k X n m hnm a t ≫ f) (projection_comp p k X m a b θ t d)).trans
      (WittTupleReductionCoordinates.morphism_projection p k X n m hnm a t (θ d)))
  have hr := (Category.assoc _ _ _).trans
    ((congrArg (fun f => (Presentation.ResolutionFaceMaps.productMap.{u + 1, u} (WittFrameFamily.Family.frame p k X n) θ t).hom ≫ f)
      (WittTupleReductionCoordinates.morphism_projection p k X n m hnm b (t ∘ θ) d)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun f => f ≫ WittFrameReduction.morphism p k X n m hnm (t (θ d)))
            (projection_comp p k X n a b θ t d))))
  exact hl.trans hr.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittTupleReductionNaturality
