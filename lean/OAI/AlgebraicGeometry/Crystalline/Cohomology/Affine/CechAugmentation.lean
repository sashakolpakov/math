import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.CechExactness
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.AugmentedSections

/-! # Cech Augmentation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.CechAugmentation.AffineCechAugmentation

noncomputable section

/-!
# The affine augmented Čech quasi-isomorphism

For a finite family generating the unit ideal, the canonical augmentation
from sections of a localizing module presheaf to its actual Čech section
complex is a quasi-isomorphism. This includes the native sheaf associated
to every module over the affine coordinate ring.
-/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.IntersectionLocalization.AffineIntersectionLocalization

universe u

variable (R : Type u) [CommRing R] {ι : Type u} [Finite ι] (s : ι → R)
  (P : (Spec (CommRingCat.of R)).Opensᵒᵖ ⥤ ModuleCat.{u} R)
  (hP : ∀ r : R, IsLocalizedModule (Submonoid.powers r)
    (P.map (IntersectionLocalization.AffineIntersectionLocalization.principal R r).leTop.op).hom)

include hP in
theorem quasiIso (hs : Ideal.span (Set.range s) = ⊤) :
    QuasiIso (Cech.AugmentedSections.CechAugmentedSections.augmentation R (Spec (CommRingCat.of R))
      (fun i => IntersectionLocalization.AffineIntersectionLocalization.principal R (s i)) P ⊤) := by
  let U := fun i => IntersectionLocalization.AffineIntersectionLocalization.principal R (s i)
  have : ∀ i, IsLocalizedModule (Submonoid.powers (s i)) (P.map (U i).leTop.op).hom :=
    fun i => hP (s i)
  have : ∀ i, IsLocalizedModule (Submonoid.powers (s i))
      ((Cech.SectionsExactness.CechSectionsExactness.restriction R (Spec (CommRingCat.of R)) U P (U i)).f 0).hom :=
    fun i => CechExactness.AffineCechExactness.cochain_localization R s P hP i 0
  refine ⟨fun n => ?_⟩
  by_cases hn : n = 0
  · subst n
    exact (Cech.AugmentedSections.CechAugmentedSections.quasiIsoAt_zero_iff R (Spec (CommRingCat.of R)) U P ⊤).mpr
      (Cech.AugmentedSections.CechAugmentedSections.global_leftExact R (Spec (CommRingCat.of R)) U P s hs)
  · let E := (evaluation (Spec (CommRingCat.of R)).Opensᵒᵖ (ModuleCat.{u} R)).obj (op ⊤)
    have hz : (((E.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((CochainComplex.single₀ (Cech.Presheaf.CechPresheaf.Presheaves R (Spec (CommRingCat.of R)))).obj P))).ExactAt n :=
      HomologicalComplex.ExactAt.of_isZero (E.map_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 P n hn))
    exact (quasiIsoAt_iff_exactAt _ n hz).mpr (CechExactness.AffineCechExactness.exactAt R s P hP hs n hn)

theorem tilde_quasiIso (M : ModuleCat.{u} R) (hs : Ideal.span (Set.range s) = ⊤) :
    QuasiIso (Cech.AugmentedSections.CechAugmentedSections.augmentation R (Spec (CommRingCat.of R))
      (fun i => IntersectionLocalization.AffineIntersectionLocalization.principal R (s i))
      (modulesSpecToSheaf.obj (tilde (R := CommRingCat.of R) M)).obj ⊤) :=
  quasiIso R s _ (isLocalizing_tilde (R := CommRingCat.of R) M) hs

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.CechAugmentation.AffineCechAugmentation
