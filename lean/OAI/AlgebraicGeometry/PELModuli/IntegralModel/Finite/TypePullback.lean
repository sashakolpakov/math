import OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Invertible
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenPullbackIs
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Type Pullback -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.TypePullback

noncomputable section

/-! Pullback preserves finite type for actual quasicoherent scheme modules,
using finite local generators and their canonical pullbacks. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem module_pullback_finiteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ((pullback f).obj M).IsFiniteType := by
  choose G hG using SheafCohomology.Projective.Quasicoherent.Scheme.Modules.exists_generatingSections_restrict_of_isFiniteType_of_isAffineOpen M
  let P := (pullback f).obj M
  have hc (U : Y.affineOpens) : Limits.PreservesColimitsOfSize.{u, u} (pullback (f ∣_ U.1)) := by
    exact (pullbackPushforwardAdjunction (f ∣_ U.1)).leftAdjoint_preservesColimits
  let e (U : Y.affineOpens) :
      SheafOfModules.unit (f ⁻¹ᵁ U.1).toScheme.ringCatSheaf ≅
        (pullback (f ∣_ U.1)).obj (SheafOfModules.unit U.1.toScheme.ringCatSheaf) :=
    (SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso (f ∣_ U.1)).symm
  let G' (U : Y.affineOpens) : (P.restrict (f ⁻¹ᵁ U.1).ι).GeneratingSections :=
    SheafOfModules.GeneratingSections.equivOfIso
      ((Quotients.FiniteDescent.OpenPullbackIs.Construction.OpenPullbackSquare.adjointPullbackSquare f U.1).app M)
      ((G U).map (pullback (f ∣_ U.1)) (e U))
  have hG' (U : Y.affineOpens) : (G' U).IsFiniteType := by
    let := hG U
    constructor
    dsimp [G', SheafOfModules.GeneratingSections.equivOfIso]
    infer_instance
  let q : P.LocalGeneratorsData :=
    { I := Y.affineOpens
      X := fun U => f ⁻¹ᵁ U.1
      coversTop := by
        rw [Opens.coversTop_iff, IsOpenCover, ← f.preimage_iSup,
          iSup_affineOpens_eq_top Y, f.preimage_top]
      generators := fun U => SheafCohomology.Projective.Quasicoherent.Scheme.Modules.generatingSectionsOverOfRestrict P (f ⁻¹ᵁ U.1) (G' U) }
  have hq : q.IsFiniteType := by
    constructor
    intro U
    let := hG' U
    exact SheafCohomology.Projective.Quasicoherent.Scheme.Modules.generatingSectionsOverOfRestrict_isFiniteType P (f ⁻¹ᵁ U.1) (G' U)
  have hshrink : q.shrink.IsFiniteType := by
    constructor
    intro i
    dsimp [SheafOfModules.LocalGeneratorsData.shrink]
    exact hq.isFiniteType i.2.choose
  exact { exists_localGeneratorsData := ⟨q.shrink, hshrink⟩ }

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.TypePullback
