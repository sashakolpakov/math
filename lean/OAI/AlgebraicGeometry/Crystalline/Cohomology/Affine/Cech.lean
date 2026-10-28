import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso

/-! # Cech -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.Cech.AffineCech

noncomputable section

/-!
# Affine comparison for the native direct Čech complex

The canonical augmentation used by the de Rham Čech construction is a
quasi-isomorphism for localizing coefficients on a finite principal cover.
In particular, this holds for the actual sheaf associated to any module.
-/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.IntersectionLocalization.AffineIntersectionLocalization

universe u

variable (R : Type u) [CommRing R] {ι : Type u} [Finite ι] (s : ι → R)

def model : Over (Spec (CommRingCat.of R)) := Over.mk (𝟙 _)

variable (P : (Spec (CommRingCat.of R)).Opensᵒᵖ ⥤ ModuleCat.{u} R)
  (hP : ∀ r : R, IsLocalizedModule (Submonoid.powers r)
    (P.map (IntersectionLocalization.AffineIntersectionLocalization.principal R r).leTop.op).hom)

include hP in
theorem quasiIso (hs : Ideal.span (Set.range s) = ⊤) :
    QuasiIso (Cech.Descent.CechDescent.augmentation R (model R) (fun i => IntersectionLocalization.AffineIntersectionLocalization.principal R (s i)) P) := by
  let U := fun i => IntersectionLocalization.AffineIntersectionLocalization.principal R (s i)
  let a := Cech.AugmentedSections.CechAugmentedSections.augmentation R (Spec (CommRingCat.of R)) U P ⊤
  have ha : QuasiIso a := CechAugmentation.AffineCechAugmentation.quasiIso R s P hP hs
  have he : QuasiIso (Cech.GlobalSectionsIso.CechGlobalSectionsIso.complexIso R (model R) U P).hom :=
    HomotopyEquiv.quasiIso_hom (HomotopyEquiv.ofIso (Cech.GlobalSectionsIso.CechGlobalSectionsIso.complexIso R (model R) U P))
  have hs₀ : QuasiIso (Cech.GlobalSectionsIso.CechGlobalSectionsIso.sourceIso R (model R) P).inv :=
    HomotopyEquiv.quasiIso_hom (HomotopyEquiv.ofIso (Cech.GlobalSectionsIso.CechGlobalSectionsIso.sourceIso R (model R) P).symm)
  have hi : QuasiIso (a ≫ (Cech.GlobalSectionsIso.CechGlobalSectionsIso.complexIso R (model R) U P).hom) :=
    quasiIso_comp a _ (hφ := ha) (hφ' := he)
  have ht : QuasiIso ((Cech.GlobalSectionsIso.CechGlobalSectionsIso.sourceIso R (model R) P).inv ≫
      a ≫ (Cech.GlobalSectionsIso.CechGlobalSectionsIso.complexIso R (model R) U P).hom) :=
    quasiIso_comp _ _ (hφ := hs₀) (hφ' := hi)
  exact (Cech.GlobalSectionsIso.CechGlobalSectionsIso.augmentation_comp R (model R) U P) ▸ ht

theorem tilde_quasiIso (M : ModuleCat.{u} R) (hs : Ideal.span (Set.range s) = ⊤) :
    QuasiIso (Cech.Descent.CechDescent.augmentation R (model R) (fun i => IntersectionLocalization.AffineIntersectionLocalization.principal R (s i))
      (modulesSpecToSheaf.obj (tilde (R := CommRingCat.of R) M)).obj) :=
  quasiIso R s _ (isLocalizing_tilde (R := CommRingCat.of R) M) hs

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.Cech.AffineCech
