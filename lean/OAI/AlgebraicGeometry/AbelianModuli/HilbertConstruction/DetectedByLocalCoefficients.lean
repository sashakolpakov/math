import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoordinateLocalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.RingSectionBasis
import Mathlib.RingTheory.LocalProperties.Submodule

/-! # Detected By Local Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DetectedByLocalCoefficients

noncomputable section

/-! An actual section vanishes if all of its pullbacks to the local
coefficient rings at maximal ideals vanish. No reducedness assumption
or finite generation of its global section module is used. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S X : Scheme.{u}} [IsAffine S] [CompactSpace X]
variable [IsAffineHom (pullback.diagonal (terminal.from X))]

theorem section_eq_zero_of_localCoefficientPullbacks
    (f : X ⟶ S) (L : Line.Bundles.LineBundle X) (s : Line.Bundles.structureModule X ⟶ L.sheaf)
    (hs : ∀ (p : Ideal Γ(S, ⊤)) [p.IsMaximal],
      Ample.LineBundles.pullbackSection (pullback.fst f
        (Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap Γ(S, ⊤) (Localization.AtPrime p)))) s = 0) : s = 0 := by
  let q (p : Ideal Γ(S, ⊤)) [p.IsMaximal] :=
    Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap Γ(S, ⊤) (Localization.AtPrime p))
  let V := (Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor f.appTop.hom).obj L.sheaf
  let W (p : Ideal Γ(S, ⊤)) [p.IsMaximal] :=
    (Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor f.appTop.hom).obj
      ((Scheme.Modules.pushforward (pullback.fst f (q p))).obj
        ((Scheme.Modules.pullback (pullback.fst f (q p))).obj L.sheaf))
  let F (p : Ideal Γ(S, ⊤)) [p.IsMaximal] : V →ₗ[Γ(S, ⊤)] W p :=
    ((Coefficient.PullbackSectionMap.coefficientPullbackSectionPresheafMap (pullback.fst f (q p)) f.appTop.hom L.sheaf).app (.op ⊤)).hom
  have hloc : ∀ (p : Ideal Γ(S, ⊤)) [p.IsMaximal], IsLocalizedModule p.primeCompl (F p) :=
    fun p _ => Affine.CoordinateLocalization.affineCoordinateLocalization_sections f L p.primeCompl (Localization.AtPrime p)
  let e := Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv f.appTop.hom L.sheaf
  have hz : e s = 0 := by
    apply @Module.eq_zero_of_localization_maximal Γ(S, ⊤) V _ _ _
      (fun p _ => W p) (fun p _ => inferInstance) (fun p _ => inferInstance)
      (fun p _ => F p) hloc (e s)
    intro p _
    have h := congrArg (Global.Sections.moduleSectionHomEquiv
      ((Scheme.Modules.pullback (pullback.fst f (q p))).obj L.sheaf)) (hs p)
    rw [Pullback.SectionGlobalValue.pullbackSection_globalValue] at h
    exact h
  exact e.injective (hz.trans e.map_zero.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DetectedByLocalCoefficients
