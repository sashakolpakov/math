import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasicOpenRestrictionLocalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.SectionLocalization
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Quasicoherent Localization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.QuasicoherentLocalization

noncomputable section

/-! Global sections of any quasicoherent sheaf on a quasi-compact separated scheme localize on every principal open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

theorem globalQuasicoherentSections_localize_of_finite_affine_cover
    {X : Scheme.{u}} [X.IsSeparated] (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : iSup U = ⊤) (hUa : ∀ i, IsAffineOpen (U i)) (r : Γ(X, ⊤)) :
    IsLocalizedModule.Away r
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf (RingHom.id Γ(X, ⊤)) M).map (X.basicOpen r).leTop.op).hom := by
  let a := ((BasicOpenModuleRestriction.basicOpenRestrictionMap M r).app (op ⊤)).hom
  have ha : IsLocalizedModule.Away r a :=
    Sheaf.SectionLocalization.sheafSections_isLocalized_of_finite_cover U (BasicOpenModuleRestriction.basicOpenRestrictionMap M r)
      (Coefficient.ModulePresheaf.coefficientModulePresheaf_isSheaf _ M)
      (Coefficient.ModulePresheaf.coefficientModulePresheaf_isSheaf _ (BasicOpenModuleRestriction.basicOpenRestrictionModule M r))
      (Submonoid.powers r) hU
      (fun i ↦ BasicOpenRestrictionLocalization.basicOpenRestrictionMap_affine_isLocalized M r ⟨U i, hUa i⟩)
      (fun i j ↦ BasicOpenRestrictionLocalization.basicOpenRestrictionMap_affine_isLocalized M r
        ⟨U i ⊓ U j, (hUa i).inf (hUa j)⟩)
  let := ha
  let e := (BasicOpenModuleRestriction.basicOpenRestrictionTopIso M r).toLinearEquiv
  have he : e.toLinearMap.comp a =
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf (RingHom.id Γ(X, ⊤)) M).map (X.basicOpen r).leTop.op).hom :=
    congrArg ModuleCat.Hom.hom (BasicOpenModuleRestriction.basicOpenRestrictionMap_top_iso M r)
  have ht := IsLocalizedModule.of_linearEquiv (Submonoid.powers r) a e
  rw [he] at ht
  exact ht

theorem globalQuasicoherentSections_localize
    {X : Scheme.{u}} [X.IsSeparated] [CompactSpace X]
    (M : X.Modules) [M.IsQuasicoherent] (r : Γ(X, ⊤)) :
    IsLocalizedModule.Away r
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf (RingHom.id Γ(X, ⊤)) M).map (X.basicOpen r).leTop.op).hom := by
  let C := X.affineCover.finiteSubcover
  have (i : C.I₀) : IsAffine (C.X i) := by
    dsimp [C]
    infer_instance
  exact globalQuasicoherentSections_localize_of_finite_affine_cover M
    (fun i : C.I₀ ↦ (C.f i).opensRange) C.iSup_opensRange
    (fun i ↦ isAffineOpen_opensRange (C.f i)) r

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.QuasicoherentLocalization
