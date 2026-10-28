import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberBilinearGluing

/-! # Fiber Section Gluing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberSectionGluing

noncomputable section

/-!
# Actual fiber-section invariance gives the raw normalized gluing equation
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberBilinearGluing OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ContractionPullback

variable {S : Scheme.{u}} {E K T : Over S} (L : Line.Bundles.LineBundle E.left)
  (p q : T ⟶ K) (i : K ⟶ E) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule K.left ⟶ Line.Fibers.fiber L i)
  (σ : Line.Fibers.fiber L (p ≫ i) ⟶ Line.Fibers.fiber L (q ≫ i))

/-- Invariance in the actual composite fibers is invariance in the two iterated pullback sheaves. -/
theorem section_gluing
    (h : Line.Fibers.pullSection L p i (p ≫ i) rfl s ≫ σ = Line.Fibers.pullSection L q i (q ≫ i) rfl s) :
    Bilinear.ContractionPullback.pulledSection p.left s ≫ FiberBilinearGluing.fiberTransport L p q i σ = Bilinear.ContractionPullback.pulledSection q.left s := by
  have ht := congrArg (fun a => a ≫ (Line.Fibers.fiberPullbackIso L q i (q ≫ i) rfl).inv) h
  change ((Bilinear.ContractionPullback.pulledSection p.left s ≫ (Line.Fibers.fiberPullbackIso L p i (p ≫ i) rfl).hom) ≫ σ) ≫
      (Line.Fibers.fiberPullbackIso L q i (q ≫ i) rfl).inv =
    (Bilinear.ContractionPullback.pulledSection q.left s ≫ (Line.Fibers.fiberPullbackIso L q i (q ≫ i) rfl).hom) ≫
      (Line.Fibers.fiberPullbackIso L q i (q ≫ i) rfl).inv at ht
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at ht
  exact ht

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberSectionGluing
