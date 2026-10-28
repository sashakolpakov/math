import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EndRingEquivalence

/-! # End Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Endomorphisms of line bundles commute with pullback through the map on global scalars. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

theorem Line.Bundles.LineBundle.globalModuleScalar_endScalar (L : Line.Bundles.LineBundle X) (φ : End L.sheaf) :
    Global.ModuleScalars.globalModuleScalar L.sheaf (L.endScalar φ) = φ :=
  L.endScalar_injective (L.endScalar_globalModuleScalar (L.endScalar φ))

theorem Line.Bundles.LineBundle.endScalar_pullback (f : Y ⟶ X) (L : Line.Bundles.LineBundle X) (φ : End L.sheaf) :
    (L.pullback f).endScalar ((Scheme.Modules.pullback f).map φ) = f.appTop (L.endScalar φ) := by
  have h := congrArg (fun ψ => (L.pullback f).endScalar ((Scheme.Modules.pullback f).map ψ))
    (Line.Bundles.LineBundle.globalModuleScalar_endScalar L φ)
  rw [Global.ScalarBaseChange.globalModuleScalar_pullback] at h
  exact h.symm.trans ((L.pullback f).endScalar_globalModuleScalar _)

theorem Line.Bundles.LineBundle.endPullback_injective_of_globalFunctions (f : Y ⟶ X) (L : Line.Bundles.LineBundle X)
    (hf : Function.Injective f.appTop) :
    Function.Injective (fun φ : End L.sheaf => (Scheme.Modules.pullback f).map φ) := by
  intro φ ψ h
  apply L.endScalar_injective
  apply hf
  exact (Line.Bundles.LineBundle.endScalar_pullback f L φ).symm.trans
    ((congrArg (L.pullback f).endScalar h).trans (Line.Bundles.LineBundle.endScalar_pullback f L ψ))

theorem Line.Bundles.LineBundle.endPullback_surjective_of_globalFunctions (f : Y ⟶ X) (L : Line.Bundles.LineBundle X)
    (hf : Function.Surjective f.appTop) :
    Function.Surjective (fun φ : End L.sheaf => (Scheme.Modules.pullback f).map φ) := by
  intro ψ
  obtain ⟨r, hr⟩ := hf ((L.pullback f).endScalar ψ)
  refine ⟨Global.ModuleScalars.globalModuleScalar L.sheaf r, ?_⟩
  change (Scheme.Modules.pullback f).map (Global.ModuleScalars.globalModuleScalar L.sheaf r) = ψ
  rw [Global.ScalarBaseChange.globalModuleScalar_pullback, hr]
  exact Line.Bundles.LineBundle.globalModuleScalar_endScalar (L.pullback f) ψ

def Line.Bundles.LineBundle.endPullbackRingEquiv (f : Y ⟶ X) (L : Line.Bundles.LineBundle X)
    (hf : Function.Bijective f.appTop) : End L.sheaf ≃+* End (L.pullback f).sheaf :=
  RingEquiv.ofBijective (LineBundle.EndRing.moduleFunctorEndRingHom (Scheme.Modules.pullback f) L.sheaf)
    ⟨Line.Bundles.LineBundle.endPullback_injective_of_globalFunctions f L hf.1,
      Line.Bundles.LineBundle.endPullback_surjective_of_globalFunctions f L hf.2⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
