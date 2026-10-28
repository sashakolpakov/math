import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittTupleReductionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameTransitionComposition

/-! # Witt Tuple Transition Composition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittTupleTransitionComposition

noncomputable section

/-! Every native Witt tuple reduction satisfies the inverse-system composition laws. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.StandardCover OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family
  WittTupleReduction

universe u v

private theorem compose_projection {C : Type u} [Category.{v} C]
    {A B D E F G : C} {f : A ⟶ B} {g : B ⟶ D} {x : A ⟶ E} {y : B ⟶ F} {z : D ⟶ G}
    {a : E ⟶ F} {b : F ⟶ G} {c : E ⟶ G}
    (hf : f ≫ y = x ≫ a) (hg : g ≫ z = y ≫ b) (hc : a ≫ b = c) :
    (f ≫ g) ≫ z = x ≫ c := by
  rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc, hc]

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

local instance separated : IsSeparated (Witt.Crystalline.wittStructureMap p k X) := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

theorem identity (n a : ℕ) (t : Fin (a + 1) → StandardCover.Index k X) : WittTupleReduction.morphism p k X n n le_rfl a t = 𝟙 _ := by
  let L := BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n
  let c := limit.cone (Discrete.functor (fun d : Fin (a + 1) => WittFrameFamily.Family.frame p k X n (t d)))
  let hc : IsLimit (L.mapCone c) := isLimitOfPreserves L (limit.isLimit _)
  apply hc.hom_ext
  rintro ⟨d⟩
  exact (WittTupleReductionCoordinates.morphism_projection p k X n n le_rfl a t d).trans
    ((congrArg (fun f => (Pi.π (fun j => WittFrameFamily.Family.frame p k X n (t j)) d).hom ≫ f)
      (WittFrameTransitionComposition.identity p k X n (t d))).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm))

theorem composition (n m l : ℕ) (hnm : n ≤ m) (hml : m ≤ l) (a : ℕ) (t : Fin (a + 1) → StandardCover.Index k X) :
    WittTupleReduction.morphism p k X n m hnm a t ≫ WittTupleReduction.morphism p k X m l hml a t =
      WittTupleReduction.morphism p k X n l (hnm.trans hml) a t := by
  let L := BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) l
  let c := limit.cone (Discrete.functor (fun d : Fin (a + 1) => WittFrameFamily.Family.frame p k X l (t d)))
  let hc : IsLimit (L.mapCone c) := isLimitOfPreserves L (limit.isLimit _)
  apply hc.hom_ext
  rintro ⟨d⟩
  exact (compose_projection
    (WittTupleReductionCoordinates.morphism_projection p k X n m hnm a t d)
    (WittTupleReductionCoordinates.morphism_projection p k X m l hml a t d)
    (WittFrameTransitionComposition.composition p k X n m l hnm hml (t d))).trans
      (WittTupleReductionCoordinates.morphism_projection p k X n l (hnm.trans hml) a t d).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittTupleTransitionComposition
