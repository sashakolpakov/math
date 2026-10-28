/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleQuasicoherent.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentSectionExtension

/-! # Section Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.SectionVanishing

noncomputable section

/-! Denominator control for actual quasicoherent sections on an affine open. Adapted from the existing projective support, using HilbertConstruction's checked intrinsic affine localization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}}

theorem affineOpen_quasicoherent_section_vanishing
    (M : X.Modules) [M.IsQuasicoherent]
    (U : X.affineOpens) (f : Γ(X, U.1)) (t : Γ(M, U.1))
    (ht : M.presheaf.map (homOfLE (X.basicOpen_le f)).op t = 0) :
    ∃ n : ℕ, f ^ n • t = 0 := by
  let N := M.restrict U.1.ι
  let g : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) := U.1.topIso.inv f
  have hTop : U.1 = U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens) :=
    U.1.ι_image_top.symm
  have hBasic : X.basicOpen f =
      U.1.ι ''ᵁ U.1.toScheme.basicOpen g := by
    exact (U.1.ι_image_basicOpen_topIso_inv f).symm
  let eTop : Γ(N, (⊤ : U.1.toScheme.Opens)) ≅ Γ(M, U.1) :=
    M.restrictAppIso U.1.ι ⊤ ≪≫
      M.presheaf.mapIso (eqToIso hTop).op
  let eBasic : Γ(N, U.1.toScheme.basicOpen g) ≅ Γ(M, X.basicOpen f) :=
    M.restrictAppIso U.1.ι (U.1.toScheme.basicOpen g) ≪≫
      M.presheaf.mapIso (eqToIso hBasic).op
  let s : Γ(N, (⊤ : U.1.toScheme.Opens)) := eTop.inv t
  have hs : N.presheaf.map (U.1.toScheme.basicOpen g).leTop.op s = 0 := by
    apply (ConcreteCategory.bijective_of_isIso eBasic.hom).1
    rw [map_zero]
    simp only [N, s, eTop, eBasic, Iso.trans_hom,
      ConcreteCategory.comp_apply, Scheme.Modules.map_restrictAppIso_hom_apply,
      Iso.trans_inv, Iso.inv_hom_id_apply, Functor.mapIso_hom,
      Functor.mapIso_inv, ← M.presheaf.map_comp_apply]
    rw [show (((eqToIso hTop).op.inv ≫
          (homOfLE (U.1.ι.image_mono
            (show U.1.toScheme.basicOpen g ≤ ⊤ from le_top))).op) ≫
          (eqToIso hBasic).op.hom) =
        (homOfLE (X.basicOpen_le f)).op by
      apply Subsingleton.elim]
    exact ht
  obtain ⟨n, hn⟩ :=
    Affine.QuasicoherentSectionExtension.affine_quasicoherent_section_vanishing
      N g s hs
  refine ⟨n, ?_⟩
  have hn' := congr(eTop.hom $hn)
  rw [map_zero] at hn'
  have hscalarOne :
      X.presheaf.map (eqToIso hTop).hom.op
          ((U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).inv g) = f := by
    dsimp [g]
    rw [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appIso]
    change X.presheaf.map (eqToIso hTop).hom.op
      (X.presheaf.map (eqToIso hTop).op.inv f) = f
    rw [← X.presheaf.map_comp_apply]
    simp
  have hscalar :
      X.presheaf.map (eqToIso hTop).hom.op
          ((U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).inv
            (g ^ n)) = f ^ n := by
    rw [map_pow, map_pow, hscalarOne]
  simp only [eTop, Iso.trans_hom, ConcreteCategory.comp_apply] at hn'
  rw [smul_restrictAppIso_hom_apply] at hn'
  simp only [Functor.mapIso_hom] at hn'
  rw [show (eqToIso hTop).op.hom = (eqToIso hTop).hom.op by
    apply Subsingleton.elim] at hn'
  rw [M.map_smul, hscalar] at hn'
  have hsection :
      M.presheaf.map (eqToIso hTop).hom.op
          ((M.restrictAppIso U.1.ι ⊤).hom s) = t := by
    change eTop.hom s = t
    exact eTop.inv_hom_id_apply t
  rw [hsection] at hn'
  exact hn'

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.SectionVanishing
