import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.PullbackSquare
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.QuasicoherenceLocality
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Morphism Quasicoherent Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.MorphismQuasicoherentPullback

noncomputable section

/-! Pullback along an affine morphism preserves actual quasicoherent modules, by restriction to affine opens. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

theorem quasicoherent_pullback_of_isAffineHom [IsAffineHom f]
    (M : Y.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pullback f).obj M).IsQuasicoherent := by
  let P := (Scheme.Modules.pullback f).obj M
  have hlocal (U : Y.affineOpens) : (P.over (f ⁻¹ᵁ U.1)).IsQuasicoherent := by
    have : IsAffine U.1.toScheme := U.2
    have : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
    have hq : ((Scheme.Modules.pullback (f ∣_ U.1)).obj
        ((Scheme.Modules.restrictFunctor U.1.ι).obj M)).IsQuasicoherent :=
      QuasicoherentPullback.affine_pullback_quasicoherent (f ∣_ U.1) _
    have : (P.restrict (f ⁻¹ᵁ U.1).ι).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent (f ⁻¹ᵁ U.1).toScheme.ringCatSheaf).prop_of_iso
        ((OpenModule.PullbackSquare.OpenPullbackSquare.adjointPullbackSquare f U.1).app M) hq
    exact Module.QuasicoherenceLocality.module_over_quasicoherent_of_affine_restriction P
      (f ⁻¹ᵁ U.1)
  have hcover : (Opens.grothendieckTopology X).CoversTop
      (fun U : Y.affineOpens => f ⁻¹ᵁ U.1) := by
    rw [Opens.coversTop_iff, IsOpenCover, ← f.preimage_iSup, iSup_affineOpens_eq_top, f.preimage_top]
  exact @SheafOfModules.IsQuasicoherent.of_coversTop _ _ _ _ _ _ _ _ P _
    (fun U : Y.affineOpens => f ⁻¹ᵁ U.1) hcover hlocal

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.MorphismQuasicoherentPullback
