import OAI.AlgebraicGeometry.SheafCohomology.Projective.AffineRankOne

/-! # Affine Rank One Restriction -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.AffineRankOneRestriction

noncomputable section

/-! An affine-open basis gives a frame of the restricted module. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u

def affineRankOneRestrictionIso {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] (U : X.affineOpens)
    (e : Γ(X, U.1) ≃ₗ[Γ(X, U.1)] Γ(M, U.1)) :
    Invertible.Scheme.Modules.unitObj U.1.toScheme ≅ M.restrict U.1.ι := by
  have he : Nonempty (Γ(X, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)) ≃ₗ[
      Γ(X, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))]
      Γ(M, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))) := by
    rw [U.1.ι_image_top]
    exact ⟨e⟩
  let e' := Classical.choice he
  let N := M.restrict U.1.ι
  let eR := U.1.ι.appIso (⊤ : U.1.toScheme.Opens)
  let eM := M.restrictAppIso U.1.ι (⊤ : U.1.toScheme.Opens)
  let x : Γ(N, ⊤) := eM.inv (e' 1)
  let f := AffineRankOne.globalGeneratorHom N x
  have hformula (r : Γ(U.1.toScheme, ⊤)) :
      eM.hom (f.val.app (op ⊤) r) = e' (eR.inv r) := by
    change eM.hom ((AffineRankOne.globalGeneratorHom N x).val.app (op ⊤) r) = _
    rw [AffineRankOne.globalGeneratorHom_top]
    rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
    change eR.inv r • eM.hom (eM.inv (e' 1)) = _
    rw [Iso.inv_hom_id_apply, ← e'.map_smul]
    simp only [smul_eq_mul, mul_one]
  have hbij : Function.Bijective (f.val.app (op ⊤)) := by
    have heM := ConcreteCategory.bijective_of_isIso eM.hom
    have hcomp : Function.Bijective (eM.hom ∘ f.val.app (op ⊤)) := by
      have hfun : eM.hom ∘ f.val.app (op ⊤) = e' ∘ eR.inv := funext hformula
      rw [hfun]
      exact e'.bijective.comp (ConcreteCategory.bijective_of_isIso eR.inv)
    refine ⟨fun a b h => hcomp.1 (congrArg eM.hom h), ?_⟩
    intro y
    obtain ⟨r, hr⟩ := hcomp.2 (eM.hom y)
    exact ⟨r, heM.1 hr⟩
  letI : IsAffine U.1.toScheme := U.2
  letI : (Invertible.Scheme.Modules.unitObj U.1.toScheme).IsQuasicoherent :=
    InvertibleFinitePresentation.invertible_quasicoherent Invertible.Scheme.Modules.isInvertible_unit
  letI : IsIso f := Quasicoherent.Scheme.Modules.isIso_of_isQuasicoherent_of_isIso_app_top f
    ((ConcreteCategory.isIso_iff_bijective (f.val.app (op ⊤))).mpr hbij)
  exact asIso f

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.AffineRankOneRestriction
