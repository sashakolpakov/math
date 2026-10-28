/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleQuasicoherent.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentSectionExtension

/-! # Section Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.SectionExtension

noncomputable section

/-! Denominator control for actual quasicoherent sections on an affine open. Adapted from the existing projective support, using HilbertConstruction's checked intrinsic affine localization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}}

theorem affineOpen_quasicoherent_section_clear_denominator
    (M : X.Modules) [M.IsQuasicoherent]
    (U : X.affineOpens) (f : Γ(X, U.1)) (s : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, U.1)),
      M.presheaf.map (homOfLE (X.basicOpen_le f)).op t =
        X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • s := by
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
  let r : Γ(N, U.1.toScheme.basicOpen g) := eBasic.inv s
  obtain ⟨n, t, ht⟩ :=
    Affine.QuasicoherentSectionExtension.affine_quasicoherent_section_clear_denominator
      N g r
  refine ⟨n, eTop.hom t, ?_⟩
  have hleft :
      M.presheaf.map (homOfLE (X.basicOpen_le f)).op (eTop.hom t) =
        eBasic.hom
          (N.presheaf.map (U.1.toScheme.basicOpen g).leTop.op t) := by
    simp only [N, eTop, eBasic, Iso.trans_hom,
      ConcreteCategory.comp_apply, Functor.mapIso_hom,
      Scheme.Modules.map_restrictAppIso_hom_apply,
      ← M.presheaf.map_comp_apply]
    exact ConcreteCategory.congr_hom
      (M.presheaf.congr_map (Subsingleton.elim _ _)) _
  have hright :
      eBasic.hom
          (U.1.toScheme.presheaf.map
              (U.1.toScheme.basicOpen g).leTop.op (g ^ n) • r) =
        X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • s := by
    change M.presheaf.map (eqToIso hBasic).op.hom
        ((M.restrictAppIso U.1.ι (U.1.toScheme.basicOpen g)).hom
          (U.1.toScheme.presheaf.map
              (U.1.toScheme.basicOpen g).leTop.op (g ^ n) • r)) = _
    rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
    have hmap := M.val.map_smul (eqToIso hBasic).op.hom
      ((U.1.ι.appIso (U.1.toScheme.basicOpen g)).inv
        (U.1.toScheme.presheaf.map
          (U.1.toScheme.basicOpen g).leTop.op (g ^ n)))
      ((M.restrictAppIso U.1.ι (U.1.toScheme.basicOpen g)).hom r)
    refine hmap.trans ?_
    have hr :
        M.val.map (eqToIso hBasic).op.hom
            ((M.restrictAppIso U.1.ι (U.1.toScheme.basicOpen g)).hom r) = s := by
      dsimp only [r]
      change eBasic.hom r = s
      exact eBasic.inv_hom_id_apply s
    rw [hr]
    let i : Opposite.op (⊤ : U.1.toScheme.Opens) ⟶
        Opposite.op (U.1.toScheme.basicOpen g) :=
      (U.1.toScheme.basicOpen g).leTop.op
    have hnat := ConcreteCategory.congr_hom
      (U.1.ι.appIso_inv_naturality i) (g ^ n)
    have hscalarOne :
        X.presheaf.map (eqToIso hTop).hom.op
            ((U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).inv g) = f := by
      dsimp only [g]
      rw [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appIso]
      change X.presheaf.map (eqToIso hTop).hom.op
        (X.presheaf.map (eqToIso hTop).op.inv f) = f
      rw [← X.presheaf.map_comp_apply]
      simp
    have hscalarTop :
        X.presheaf.map (eqToIso hTop).hom.op
            ((U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).inv (g ^ n)) =
          f ^ n := by
      rw [map_pow, map_pow, hscalarOne]
    have hscalar :
        X.presheaf.map (eqToIso hBasic).op.hom
            ((U.1.ι.appIso (U.1.toScheme.basicOpen g)).inv
              (U.1.toScheme.presheaf.map i (g ^ n))) =
          X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) := by
      calc
        X.presheaf.map (eqToIso hBasic).op.hom
            ((U.1.ι.appIso (U.1.toScheme.basicOpen g)).inv
              (U.1.toScheme.presheaf.map i (g ^ n))) =
            X.presheaf.map (eqToIso hBasic).op.hom
              (X.presheaf.map (U.1.ι.opensFunctor.op.map i)
                ((U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).inv (g ^ n))) := by
              exact congrArg
                (fun y ↦ X.presheaf.map (eqToIso hBasic).op.hom y) hnat
        _ = X.presheaf.map (homOfLE (X.basicOpen_le f)).op
            (X.presheaf.map (eqToIso hTop).hom.op
              ((U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).inv (g ^ n))) := by
              rw [← X.presheaf.map_comp_apply, ← X.presheaf.map_comp_apply]
              exact ConcreteCategory.congr_hom
                (X.presheaf.congr_map (Subsingleton.elim _ _)) _
        _ = X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) := by
              rw [hscalarTop]
    exact congrArg (fun z : Γ(X, X.basicOpen f) ↦ z • s) hscalar
  exact hleft.trans ((congrArg eBasic.hom ht).trans hright)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.SectionExtension
