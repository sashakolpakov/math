import OAI.AlgebraicGeometry.Crystalline.Cohomology.SuccessiveModule
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Intersection Localization -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.IntersectionLocalization.AffineIntersectionLocalization

noncomputable section

/-!
# Localization of sections on principal-open intersections

A presheaf whose global restriction maps are principal module
localizations has the same property on intersections of principal opens.
In particular this applies to the actual sheaf associated to any module.
-/

open _root_.CategoryTheory Opposite _root_.AlgebraicGeometry PrimeSpectrum

universe u

variable (R : Type u) [CommRing R]

abbrev principal (r : R) : (Spec (CommRingCat.of R)).Opens := basicOpen r

theorem principal_mul (b s : R) : principal R (b * s) = principal R b ⊓ principal R s :=
  basicOpen_mul b s

variable (P : (Spec (CommRingCat.of R)).Opensᵒᵖ ⥤ ModuleCat.{u} R)
  (hP : ∀ r : R, IsLocalizedModule (Submonoid.powers r)
    (P.map (principal R r).leTop.op).hom)

include hP in
theorem restriction (b s : R) :
    IsLocalizedModule (Submonoid.powers s)
      (P.map (homOfLE inf_le_right : principal R s ⊓ principal R b ⟶ principal R b).op).hom := by
  let f := (P.map (principal R b).leTop.op).hom
  let g := (P.map (homOfLE inf_le_right : principal R s ⊓ principal R b ⟶ principal R b).op).hom
  have : IsLocalizedModule.Away b f := hP b
  have : IsLocalizedModule.Away (b * s) (g.comp f) := by
    change IsLocalizedModule (Submonoid.powers (b * s))
      (P.map (principal R b).leTop.op ≫
        P.map (homOfLE inf_le_right : principal R s ⊓ principal R b ⟶ principal R b).op).hom
    rw [← P.map_comp]
    have h := hP (b * s)
    rw [principal_mul, inf_comm] at h
    exact h
  exact SuccessiveModule.SuccessiveModuleLocalization.isLocalizedModule R _ _ _ b s f g

include hP in
theorem intersection (V : (Spec (CommRingCat.of R)).Opens) (b s : R)
    (hV : V = principal R b) :
    IsLocalizedModule (Submonoid.powers s)
      (P.map (homOfLE (inf_le_inf_right V le_top) :
        principal R s ⊓ V ⟶ ⊤ ⊓ V).op).hom := by
  subst V
  let e : P.obj (op (⊤ ⊓ principal R b)) ≅ P.obj (op (principal R b)) :=
    P.mapIso (eqToIso (congrArg op (top_inf_eq (a := principal R b))))
  let g := P.map (homOfLE inf_le_right : principal R s ⊓ principal R b ⟶ principal R b).op
  have hg : IsLocalizedModule (Submonoid.powers s) g.hom := restriction R P hP b s
  have he : P.map (homOfLE (inf_le_inf_right (principal R b) le_top) :
      principal R s ⊓ principal R b ⟶ ⊤ ⊓ principal R b).op = e.hom ≫ g := by
    dsimp only [e, g, Functor.mapIso_hom]
    rw [← P.map_comp]
    congr 1
  rw [he]
  exact IsLocalizedModule.of_linearEquiv_right (Submonoid.powers s) g.hom e.toLinearEquiv

theorem tilde_restriction (M : ModuleCat.{u} R) (b s : R) :
    IsLocalizedModule (Submonoid.powers s)
      ((modulesSpecToSheaf.obj (tilde (R := CommRingCat.of R) M)).obj.map
        (homOfLE inf_le_right : principal R s ⊓ principal R b ⟶ principal R b).op).hom :=
  restriction R _ (isLocalizing_tilde (R := CommRingCat.of R) M) b s

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.IntersectionLocalization.AffineIntersectionLocalization
