import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.TranslatedRestrictions
import OAI.RepresentationTheory.Theta.Geometric.LocallyConstantFiberMap

/-! # Locally Translated Iso Naturality -/

namespace OAI.RepresentationTheory.Theta.Geometric.LocallyTranslatedIsoNaturality

noncomputable section

/-! The glued comparison commutes with arbitrary base change whenever
its locally constant labels do. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations
universe u

theorem locallyTranslatedIso_naturality {X T U : Scheme.{u}} (M : X.Modules)
    {I : Type u} (t : I → (X ⟶ X)) (e : ∀ a, (Scheme.Modules.pullback (t a)).obj M ≅ M)
    (c : LocallyConstant T I) (d : LocallyConstant U I) (r : U ⟶ T) (hd : ∀ u, d u = c (r u))
    (x y : T ⟶ X) (x' y' : U ⟶ X) (hx : r ≫ x = x') (hy : r ≫ y = y')
    (h : ∀ a, (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c a).ι ≫ y = ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c a).ι ≫ x) ≫ t a)
    (h' : ∀ a, (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber d a).ι ≫ y' = ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber d a).ι ≫ x') ≫ t a)
    (φ : (Scheme.Modules.pullback y).obj M ⟶ (Scheme.Modules.pullback x).obj M)
    (ψ : (Scheme.Modules.pullback y').obj M ⟶ (Scheme.Modules.pullback x').obj M)
    (hφ : ∀ a, (Scheme.Modules.pullback (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c a).ι).map φ =
      (LocallyTranslatedLineIso.restrictedTranslatedMapLineIso M (t a) (e a) x y (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c a) (h a)).hom)
    (hψ : ∀ a, (Scheme.Modules.pullback (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber d a).ι).map ψ =
      (LocallyTranslatedLineIso.restrictedTranslatedMapLineIso M (t a) (e a) x' y' (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber d a) (h' a)).hom) :
    AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations.nativePullback φ r y' x' hy hx = ψ := by
  apply Intrinsic.PullbackCoherence.nativePullback_ext_open_cover _ ψ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber d) (by
    apply top_unique
    intro u _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨d u, rfl⟩)
  intro a
  let v := (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber d a).ι
  have hn := Intrinsic.PullbackCoherence.nativePullback_nested φ r y' x' hy hx v (v ≫ y') (v ≫ x') rfl rfl
  have hf := Intrinsic.TranslatedRestrictions.nativePullback_glued_translation_of_factor M (t a) (e a) x y
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c a) (h a) φ (hφ a) (v ≫ r)
    (LocallyConstantFiberMap.locallyConstantFiberMap r c d hd a) (LocallyConstantFiberMap.locallyConstantFiberMap_fac r c d hd a)
    (v ≫ x') (v ≫ y') (by rw [Category.assoc, hx]) (by rw [Category.assoc, hy]) (h' a)
  have hp := Intrinsic.TranslatedRestrictions.nativePullback_restrictedTranslatedMapLineIso M (t a) (e a) x' y'
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber d a) (h' a) ψ (hψ a)
  exact hn.trans (hf.trans hp.symm)

end

end OAI.RepresentationTheory.Theta.Geometric.LocallyTranslatedIsoNaturality
