import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.AdjunctionUnit
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FiniteGeneratingSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentFiniteTypeSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.RestrictionFiniteType
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictionGeneratingSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Pullback Finite Type -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.PullbackFiniteType

noncomputable section

/-! Pullback preserves finite type for actual quasicoherent scheme modules,
using finite local generators and their canonical pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem module_pullback_finiteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ((pullback f).obj M).IsFiniteType := by
  have hlocal (U : Y.affineOpens) :
      ∃ G : (M.restrict U.1.ι).GeneratingSections, G.IsFiniteType := by
    have : IsAffine U.1.toScheme := U.2
    have : (M.restrict U.1.ι).IsFiniteType := RestrictionFiniteType.quasicoherent_openRestrict_finiteType U.1.ι M
    have : Module.Finite Γ(U.1.toScheme, ⊤) Γ(M.restrict U.1.ι, ⊤) :=
      Affine.QuasicoherentFiniteTypeSections.affine_quasicoherent_finiteType_sections_finite (M.restrict U.1.ι)
    exact Affine.FiniteGeneratingSections.affine_exists_finite_generatingSections (M.restrict U.1.ι)
  choose G hG using hlocal
  let P := (pullback f).obj M
  have hc (U : Y.affineOpens) : Limits.PreservesColimitsOfSize.{u, u} (pullback (f ∣_ U.1)) := by
    exact (pullbackPushforwardAdjunction (f ∣_ U.1)).leftAdjoint_preservesColimits
  let e (U : Y.affineOpens) :
      SheafOfModules.unit (f ⁻¹ᵁ U.1).toScheme.ringCatSheaf ≅
        (pullback (f ∣_ U.1)).obj (SheafOfModules.unit U.1.toScheme.ringCatSheaf) :=
    (Line.Bundles.structureModulePullbackIso (f ∣_ U.1)).symm
  let G' (U : Y.affineOpens) : (P.restrict (f ⁻¹ᵁ U.1).ι).GeneratingSections :=
    SheafOfModules.GeneratingSections.equivOfIso
      ((OpenModule.PullbackSquare.OpenPullbackSquare.adjointPullbackSquare f U.1).app M)
      (@SheafOfModules.GeneratingSections.map _ _ _ _ _ _ _ _ _ _ _ _ _
        (G U) (pullback (f ∣_ U.1)) (hc U) (e U))
  have hG' (U : Y.affineOpens) : (G' U).IsFiniteType := by
    constructor
    change Finite (G U).I
    exact (hG U).finite
  let q : P.LocalGeneratorsData :=
    { I := Y.affineOpens
      X := fun U => f ⁻¹ᵁ U.1
      coversTop := by
        rw [Opens.coversTop_iff, IsOpenCover, ← f.preimage_iSup,
          iSup_affineOpens_eq_top Y, f.preimage_top]
      generators := fun U => RestrictionGeneratingSections.generatingSectionsOverOfRestrict P (f ⁻¹ᵁ U.1) (G' U) }
  have hq : q.IsFiniteType := by
    constructor
    intro U
    let := hG' U
    exact RestrictionGeneratingSections.generatingSectionsOverOfRestrict_isFiniteType P (f ⁻¹ᵁ U.1) (G' U)
  have hshrink : q.shrink.IsFiniteType := by
    constructor
    intro i
    dsimp [SheafOfModules.LocalGeneratorsData.shrink]
    exact hq.isFiniteType i.2.choose
  exact { exists_localGeneratorsData := ⟨q.shrink, hshrink⟩ }

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.PullbackFiniteType
