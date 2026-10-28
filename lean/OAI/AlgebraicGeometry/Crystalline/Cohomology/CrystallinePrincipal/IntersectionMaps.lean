import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Functor

/-! # Intersection Maps -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.IntersectionMaps.CrystallinePrincipalIntersectionMaps

noncomputable section

/-!
# Native principal-intersection maps and the usual fraction maps

The native maps from D(s*t) to D(s) and D(t) commute over their original
crystalline object. Their ambient maps are exactly the standard maps of
principal localizations used by the affine ring sheaf gluing theorem.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q : Site.Object p k X)
  (s t : Q.thickening.ring)

local notation "QR" => Q.thickening.ring

def leftCoefficient : (⟨s * t⟩ : PrincipalCoefficient.PrincipalCoefficientCategory.Object QR) ⟶ ⟨s⟩ :=
  homOfLE (by
    change PrimeSpectrum.basicOpen (s * t) ≤ PrimeSpectrum.basicOpen s
    rw [PrimeSpectrum.basicOpen_mul]
    exact inf_le_left)

def rightCoefficient : (⟨s * t⟩ : PrincipalCoefficient.PrincipalCoefficientCategory.Object QR) ⟶ ⟨t⟩ :=
  homOfLE (by
    change PrimeSpectrum.basicOpen (s * t) ≤ PrimeSpectrum.basicOpen t
    rw [PrimeSpectrum.basicOpen_mul]
    exact inf_le_right)

def left : Opens.CrystallinePrincipalOpens.object p k X Q (s * t) ⟶ Opens.CrystallinePrincipalOpens.object p k X Q s :=
  Functor.CrystallinePrincipalFunctor.map p k X Q (leftCoefficient p k X Q s t)

def right : Opens.CrystallinePrincipalOpens.object p k X Q (s * t) ⟶ Opens.CrystallinePrincipalOpens.object p k X Q t :=
  Functor.CrystallinePrincipalFunctor.map p k X Q (rightCoefficient p k X Q s t)

theorem condition : left p k X Q s t ≫ Opens.CrystallinePrincipalOpens.projection p k X Q s =
    right p k X Q s t ≫ Opens.CrystallinePrincipalOpens.projection p k X Q t :=
  (Functor.CrystallinePrincipalFunctor.map_projection p k X Q (leftCoefficient p k X Q s t)).trans
    (Functor.CrystallinePrincipalFunctor.map_projection p k X Q (rightCoefficient p k X Q s t)).symm

theorem left_ambient : (left p k X Q s t).ambientMap.toRingHom =
    IsLocalization.Away.awayToAwayRight (S := Localization.Away s) (P := Localization.Away (s * t)) s t := by
  apply IsLocalization.ringHom_ext (S := Localization.Away s) (Submonoid.powers s)
  ext x
  exact (Functor.CrystallinePrincipalFunctor.map_algebraMap p k X Q (leftCoefficient p k X Q s t) x).trans
    (IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away s) (P := Localization.Away (s * t)) s t x).symm

theorem right_ambient : (right p k X Q s t).ambientMap.toRingHom =
    IsLocalization.Away.awayToAwayLeft (S := Localization.Away t) (P := Localization.Away (s * t)) t s := by
  apply IsLocalization.ringHom_ext (S := Localization.Away t) (Submonoid.powers t)
  ext x
  exact (Functor.CrystallinePrincipalFunctor.map_algebraMap p k X Q (rightCoefficient p k X Q s t) x).trans
    (IsLocalization.Away.awayToAwayLeft_eq (S := Localization.Away t) (P := Localization.Away (s * t)) t s x).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.IntersectionMaps.CrystallinePrincipalIntersectionMaps
