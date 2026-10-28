import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.QuasicoherentLocalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.RankOneBasisTransport

/-! # Principal Rank One Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PrincipalRankOneSections

noncomputable section

/-! A rank-one basis of localized global sections gives an actual section basis on the corresponding principal open. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}} [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]

def affinePrincipalRankOneSections (r : Γ(X, ⊤))
    (e : LocalizedModule.Away r Γ(M, ⊤) ≃ₗ[Localization.Away r] Localization.Away r) :
    Γ(M, X.basicOpen r) ≃ₗ[Γ(X, X.basicOpen r)] Γ(X, X.basicOpen r) := by
  let R := Γ(X, ⊤)
  let B := Γ(X, X.basicOpen r)
  let L := Γ(M, X.basicOpen r)
  letI : Module R L := Module.compHom _ (algebraMap R B)
  letI : IsScalarTower R B L := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : IsLocalization.Away r B := (isAffineOpen_top X).isLocalization_basicOpen r
  let φ : Γ(M, ⊤) →ₗ[R] L := {
    toFun := M.presheaf.map (homOfLE (X.basicOpen_le r)).op
    map_add' := (M.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom.map_add
    map_smul' := fun a x => M.map_smul (homOfLE (X.basicOpen_le r)) a x }
  haveI : IsLocalizedModule.Away r φ :=
    AffineOpen.QuasicoherentLocalization.affineOpen_quasicoherent_sections_localize M ⟨⊤, isAffineOpen_top X⟩ r
  exact Localized.RankOneBasisTransport.localizedRankOneBasisTransport (.powers r) φ e

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PrincipalRankOneSections
