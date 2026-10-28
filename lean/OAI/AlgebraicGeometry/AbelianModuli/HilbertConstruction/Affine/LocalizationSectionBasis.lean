import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.BasisCoefficientTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.SectionBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalSectionsFunctor
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Localization Section Basis -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.LocalizationSectionBasis

noncomputable section

/-! A basis of localized global sections gives a complete basis of the
actual pulled-back line bundle on the corresponding affine localization point. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S X : Scheme.{u}} [IsAffine S] (f : X ⟶ S) [IsProper f]

theorem affineLocalizationPoint_isOpenImmersion (r : Γ(S, ⊤)) :
    IsOpenImmersion (QuotientCoefficientMap.affineCoordinateMap (algebraMap Γ(S, ⊤) (Localization.Away r))) := by
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (Localization.Away r)))) :=
    IsOpenImmersion.of_isLocalization r
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (algebraMap Γ(S, ⊤) (Localization.Away r))) ≫ S.isoSpec.inv)
  infer_instance

def affineLocalizationSectionBasis (L : Line.Bundles.LineBundle X) (r : Γ(S, ⊤)) {ι : Type v}
    (B : Module.Basis ι (Localization.Away r)
      (LocalizedModule.Away r ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor f.appTop.hom).obj L.sheaf))) :
    Module.Basis ι Γ(Spec (.of (Localization.Away r)), ⊤)
      ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor (pullback.snd f
        (QuotientCoefficientMap.affineCoordinateMap (algebraMap Γ(S, ⊤) (Localization.Away r)))).appTop.hom).obj
          (L.pullback (pullback.fst f
            (QuotientCoefficientMap.affineCoordinateMap (algebraMap Γ(S, ⊤) (Localization.Away r))))).sheaf) := by
  let A := Localization.Away r
  let b := QuotientCoefficientMap.affineCoordinateMap (algebraMap Γ(S, ⊤) A)
  letI : Algebra A (TensorSectionComparison.morphismGlobalAlgebra b) := (Scheme.ΓSpecIso (.of A)).inv.hom.toAlgebra
  letI : IsScalarTower Γ(S, ⊤) A (TensorSectionComparison.morphismGlobalAlgebra b) :=
    IsScalarTower.of_algebraMap_eq (fun c => RingHom.congr_fun
      (Localized.BasisCoefficientTransport.affineCoordinateMap_appTop (algebraMap Γ(S, ⊤) A)) c)
  have : IsOpenImmersion b := affineLocalizationPoint_isOpenImmersion r
  have : Module.Flat Γ(S, ⊤) (TensorSectionComparison.morphismGlobalAlgebra b) :=
    RingHom.flat_algebraMap_iff.mp b.flat_appTop
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  exact (Localized.BasisCoefficientTransport.localizedModuleBasis_baseChange r (TensorSectionComparison.morphismGlobalAlgebra b) B).map
    (Scalar.SectionBaseChange.flat_lineBundleGlobalSectionsEquiv (IsPullback.of_hasPullback f b) L)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.LocalizationSectionBasis
