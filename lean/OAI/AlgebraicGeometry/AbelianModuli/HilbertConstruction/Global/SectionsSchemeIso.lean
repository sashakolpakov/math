import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalSectionsPushforward
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues

/-! # Sections Scheme Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.SectionsSchemeIso

noncomputable section

/-! Pullback along an isomorphism preserves actual global sections as modules over the structural coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]

def schemeGlobalSectionsPullbackIso (f : X ⟶ Y) [IsIso f] (p : Y ⟶ Spec (.of R)) (M : Y.Modules) :
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M ≃ₗ[R]
      (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (f ≫ p)).obj ((Scheme.Modules.pullback f).obj M) := by
  let α := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M
  have hU : (⊤ : Y.Opens) ≤ f.opensRange := by
    intro y _
    exact f.homeomorph.surjective y
  have : IsIso (α.app ⊤) := OpenPullback.ModuleValues.openPullbackUnit_app_isIso f M ⊤ hU
  have : IsIso ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).map α) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (ConcreteCategory.bijective_of_isIso (α.app ⊤))
  exact (asIso ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).map α)).toLinearEquiv.trans
    (Coefficient.GlobalSectionsPushforward.schemeGlobalSectionsPushforwardIso f p ((Scheme.Modules.pullback f).obj M))

def schemeGlobalSectionsCongr (f : X ⟶ Y) [IsIso f] (p : Y ⟶ Spec (.of R))
    {M : Y.Modules} {L : X.Modules} (e : (Scheme.Modules.pullback f).obj M ≅ L) :
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M ≃ₗ[R] (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (f ≫ p)).obj L :=
  (schemeGlobalSectionsPullbackIso f p M).trans (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsIso (f ≫ p) e)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.SectionsSchemeIso
