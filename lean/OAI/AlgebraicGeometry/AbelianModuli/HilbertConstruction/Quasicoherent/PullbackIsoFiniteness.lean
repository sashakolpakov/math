import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.RestrictionFiniteType

/-! # Pullback Iso Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.PullbackIsoFiniteness

noncomputable section

/-! Pullback along an open immersion, including a scheme isomorphism, preserves coherent finite type. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem module_openPullback_quasicoherent {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) [M.IsQuasicoherent] :
    ((pullback f).obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((restrictFunctorIsoPullback f).app M) inferInstance

theorem module_openPullback_finiteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ((pullback f).obj M).IsFiniteType := by
  have : (M.restrict f).IsFiniteType := RestrictionFiniteType.quasicoherent_openRestrict_finiteType f M
  have : ((pullback f).obj M).IsQuasicoherent := module_openPullback_quasicoherent f M
  exact RestrictionFiniteType.quasicoherent_finiteType_of_iso ((restrictFunctorIsoPullback f).app M)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.PullbackIsoFiniteness
