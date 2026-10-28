import Mathlib.AlgebraicGeometry.Morphisms.Separated
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.BasicOpenModuleRestriction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SheafSectionsLocalization
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Global Basic Open Localization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.GlobalBasicOpenLocalization

noncomputable section

/-! Global sections of a quasicoherent module on a quasi-compact
separated scheme localize on every basic open. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem globalBasicOpen_isLocalized_of_finite_affine_cover
    {X : Scheme.{u}} [X.IsSeparated] (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : iSup U = ⊤) (hUa : ∀ i, IsAffineOpen (U i)) (r : Γ(X, ⊤)) :
    IsLocalizedModule.Away r
      ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (𝟙 X) M).map (X.basicOpen r).leTop.op).hom := by
  let a := ((BasicOpenModuleRestriction.basicOpenRestrictionMap M r).hom.app (op ⊤)).hom
  have ha : IsLocalizedModule.Away r a :=
    SheafSectionsLocalization.sheafSections_isLocalized_of_finite_cover U (BasicOpenModuleRestriction.basicOpenRestrictionMap M r)
      (Submonoid.powers r) hU
      (fun i => BasicOpenModuleRestriction.basicOpenRestrictionMap_affine_isLocalized M r ⟨U i, hUa i⟩)
      (fun i j => BasicOpenModuleRestriction.basicOpenRestrictionMap_affine_isLocalized M r
        ⟨U i ⊓ U j, (hUa i).inf (hUa j)⟩)
  let := ha
  let e := (BasicOpenModuleRestriction.basicOpenRestrictionTopIso M r).toLinearEquiv
  have he : e.toLinearMap.comp a =
      ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (𝟙 X) M).map (X.basicOpen r).leTop.op).hom :=
    congrArg ModuleCat.Hom.hom (BasicOpenModuleRestriction.basicOpenRestrictionMap_top_iso M r)
  have ht := IsLocalizedModule.of_linearEquiv (Submonoid.powers r) a e
  rw [he] at ht
  exact ht

theorem globalBasicOpen_isLocalized
    {X : Scheme.{u}} [X.IsSeparated] [CompactSpace X]
    (M : X.Modules) [M.IsQuasicoherent] (r : Γ(X, ⊤)) :
    IsLocalizedModule.Away r
      ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (𝟙 X) M).map (X.basicOpen r).leTop.op).hom := by
  let C := X.affineCover.finiteSubcover
  have (i : C.I₀) : IsAffine (C.X i) := by
    dsimp [C]
    infer_instance
  exact globalBasicOpen_isLocalized_of_finite_affine_cover M
    (fun i : C.I₀ => (C.f i).opensRange) C.iSup_opensRange
    (fun i => isAffineOpen_opensRange (C.f i)) r

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.GlobalBasicOpenLocalization
