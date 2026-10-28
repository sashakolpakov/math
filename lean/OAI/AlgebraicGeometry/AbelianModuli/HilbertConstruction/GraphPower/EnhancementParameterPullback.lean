import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementFamilyTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterLevelPointComparison

/-! # Enhancement Parameter Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower

noncomputable section

/-! Graph-power polarization enhancements are stable under changes of
parameter points, using the actual canonical Cartesian family comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable {F : Level.Data.AbelianSchemeWithFullLevel g N S} {L : Line.Bundles.LineBundle F.abelian.scheme.left} {d : ℕ}
variable {U T : Over S}

def PolarizationEnhancementData.GraphPowerPolarizationEnhancement.parameterPullback
    (D : PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback T.hom)
      (L.pullback (CategoryTheory.Limits.pullback.fst F.abelian.scheme.hom T.hom)) d) (f : U ⟶ T) :
    PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback U.hom)
      (L.pullback (CategoryTheory.Limits.pullback.fst F.abelian.scheme.hom U.hom)) d := by
  let e := (F.abelian.parameterPullbackIso f).symm
  letI : IsMonHom e.hom := Abelian.Schemes.AbelianScheme.parameterPullbackIso_symm_isMonHom f F.abelian
  let a := CategoryTheory.Limits.pullback.fst F.abelian.scheme.hom U.hom
  let b := CategoryTheory.Limits.pullback.fst F.abelian.scheme.hom T.hom
  let c := CategoryTheory.Limits.pullback.fst (F.abelian.pullback T.hom).scheme.hom f.left
  have h : e.hom.left ≫ a = c ≫ b :=
    ParameterLevelPointComparison.singleParameterBaseChangeIso_inv_original_fst f F.abelian.scheme
  let eL : ((L.pullback a).pullback e.hom.left).sheaf ≅ ((L.pullback b).pullback c).sheaf :=
    (Scheme.Modules.pullbackComp e.hom.left a).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr h).app L.sheaf ≪≫
        (Scheme.Modules.pullbackComp c b).symm.app L.sheaf
  exact (D.pullback f.left).transportFamily (G := F.pullback U.hom) e (Quotient.sound ⟨eL⟩)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower
