import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.VanishingOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.IsoImage

/-! # Module Zero Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModuleZeroCriterion

noncomputable section

/-! An affine quasicoherent sheaf vanishes exactly when its actual global section module vanishes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules
universe u

theorem module_sections_subsingleton_of_isZero {X : Scheme.{u}}
    (M : X.Modules) (hM : IsZero M) (U : X.Opens) : Subsingleton Γ(M, U) := by
  have hz (x : Γ(M, U)) : x = 0 := by
    have h := congrArg (fun a : M ⟶ M => a.app U x) (hM.eq_of_src (𝟙 M) 0)
    exact h
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

theorem affineModule_isZero_iff_globalSections_subsingleton
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules) [M.IsQuasicoherent] :
    IsZero M ↔ Subsingleton Γ(M, ⊤) := by
  refine ⟨fun h ↦ module_sections_subsingleton_of_isZero M h ⊤, fun h ↦ ?_⟩
  let N := (pushforward X.toSpecΓ).obj M
  have : N.IsQuasicoherent := Quasicoherent.IsoImage.modulePushforward_quasicoherent_of_isIso X.toSpecΓ M
  have : Subsingleton (moduleSpecΓFunctor.obj N) := h
  have hΓ : IsZero (moduleSpecΓFunctor.obj N) := ModuleCat.isZero_of_subsingleton _
  have hT : IsZero (tilde (moduleSpecΓFunctor.obj N)) := (tilde.functor _).map_isZero hΓ
  have : IsIso N.fromTildeΓ := inferInstance
  have hN : IsZero N := hT.of_iso (asIso N.fromTildeΓ).symm
  exact ((restrictFunctorAdjCounitIso X.toSpecΓ).app M).isZero_iff.mp
    ((restrictFunctor X.toSpecΓ).map_isZero hN)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModuleZeroCriterion
