import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BundleMapOf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EndTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EffectiveEpiFunctionDescent

/-! # End Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Effective descent of endomorphisms of a pulled-back line bundle. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

theorem Line.Bundles.LineBundle.endScalar_pullbackMapComp (a : Z ⟶ Y) (f : Y ⟶ X) (L : Line.Bundles.LineBundle X)
    (φ : End (L.pullback f).sheaf) :
    (L.pullback (a ≫ f)).endScalar (Pullback.BundleMapComposition.pullbackBundleMapComp a f φ) =
      a.appTop ((L.pullback f).endScalar φ) :=
  (Line.Bundles.LineBundle.endScalar_transport ((L.pullback f).pullback a) (L.pullback (a ≫ f))
    ((Scheme.Modules.pullbackComp a f).app L.sheaf) ((Scheme.Modules.pullback a).map φ)).trans
      (Line.Bundles.LineBundle.endScalar_pullback a (L.pullback f) φ)

theorem LineBundle.EndDescent.bundleEndDescentCondition_scalar (f : Y ⟶ X) (L : Line.Bundles.LineBundle X)
    (φ : End (L.pullback f).sheaf) (hφ : BundleMapOf.BundleMapDescentCondition f φ) :
    (pullback.fst f f).appTop ((L.pullback f).endScalar φ) =
      (pullback.snd f f).appTop ((L.pullback f).endScalar φ) := by
  have h := Line.Bundles.LineBundle.endScalar_transport_eq (L.pullback (pullback.fst f f ≫ f))
    (L.pullback (pullback.snd f f ≫ f))
    ((Scheme.Modules.pullbackCongr (pullback.condition (f := f) (g := f))).app L.sheaf)
    (Pullback.BundleMapComposition.pullbackBundleMapComp (pullback.fst f f) f φ)
    (Pullback.BundleMapComposition.pullbackBundleMapComp (pullback.snd f f) f φ) hφ.w
  exact (L.endScalar_pullbackMapComp (pullback.fst f f) f φ).symm.trans
    (h.trans (L.endScalar_pullbackMapComp (pullback.snd f f) f φ))

theorem Line.Bundles.LineBundle.existsUnique_end_descent (f : Y ⟶ X) [EffectiveEpi f] (L : Line.Bundles.LineBundle X)
    (φ : End (L.pullback f).sheaf) (hφ : BundleMapOf.BundleMapDescentCondition f φ) :
    ∃! ψ : End L.sheaf, (Scheme.Modules.pullback f).map ψ = φ := by
  obtain ⟨r, hr, _⟩ := EffectiveEpiFunctionDescent.effectiveEpi_existsUnique_globalFunction f ((L.pullback f).endScalar φ)
    (LineBundle.EndDescent.bundleEndDescentCondition_scalar f L φ hφ)
  have h : (Scheme.Modules.pullback f).map (Global.ModuleScalars.globalModuleScalar L.sheaf r) = φ := by
    rw [Global.ScalarBaseChange.globalModuleScalar_pullback, hr]
    exact Line.Bundles.LineBundle.globalModuleScalar_endScalar (L.pullback f) φ
  refine ⟨Global.ModuleScalars.globalModuleScalar L.sheaf r, h, ?_⟩
  intro ψ hψ
  exact Line.Bundles.LineBundle.endPullback_injective_of_globalFunctions f L (EffectiveEpiFunctionDescent.effectiveEpi_appTop_injective f)
    (hψ.trans h.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
