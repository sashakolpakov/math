import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.IntersectionLocalization
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.PrincipalIntersections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PresheafProduct
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.SectionsExactness

/-! # Cech Exactness -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.CechExactness.AffineCechExactness

noncomputable section

/-!
# Affine Čech exactness for actual module sheaves

For a finite unit-ideal family, every cochain module localizes to the
sections over a cover member. The explicit local Čech contraction and
the algebraic image-descent theorem therefore give global exactness in
every positive degree, including for the native tilde sheaf of a module.
-/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry PrimeSpectrum

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.IntersectionLocalization.AffineIntersectionLocalization

universe u

variable (R : Type u) [CommRing R] {ι : Type u} [Finite ι] (s : ι → R)
  (P : (Spec (CommRingCat.of R)).Opensᵒᵖ ⥤ ModuleCat.{u} R)
  (hP : ∀ r : R, IsLocalizedModule (Submonoid.powers r)
    (P.map (IntersectionLocalization.AffineIntersectionLocalization.principal R r).leTop.op).hom)

include hP in
theorem cochain_localization (i : ι) (n : ℕ) :
    IsLocalizedModule (Submonoid.powers (s i))
      ((Cech.SectionsExactness.CechSectionsExactness.restriction R (Spec (CommRingCat.of R))
        (fun j => IntersectionLocalization.AffineIntersectionLocalization.principal R (s j)) P (IntersectionLocalization.AffineIntersectionLocalization.principal R (s i))).f n).hom := by
  let F := fun v : Fin (n + 1) → ι =>
    Cech.Presheaf.CechPresheaf.intersection R (Spec (CommRingCat.of R)) P
      (∏ᶜ (fun a => (IntersectionLocalization.AffineIntersectionLocalization.principal R (s (v a)) : (Spec (CommRingCat.of R)).Opens)))
  have : ∀ v, IsLocalizedModule (Submonoid.powers (s i))
      ((F v).map (IntersectionLocalization.AffineIntersectionLocalization.principal R (s i)).leTop.op).hom := by
    intro v
    have hv : (∏ᶜ (fun a => IntersectionLocalization.AffineIntersectionLocalization.principal R (s (v a)))) = IntersectionLocalization.AffineIntersectionLocalization.principal R (∏ a, s (v a)) :=
      Cohomology.Finite.PrincipalIntersections.FinitePrincipalIntersections.categoricalProduct R (fun a => s (v a))
    exact IntersectionLocalization.AffineIntersectionLocalization.intersection R P hP _ (∏ a, s (v a)) (s i) hv
  change IsLocalizedModule (Submonoid.powers (s i))
    ((∏ᶜ F).map (IntersectionLocalization.AffineIntersectionLocalization.principal R (s i)).leTop.op).hom
  exact PresheafProduct.PresheafProductLocalization.isLocalizedModule R (Submonoid.powers (s i)) F _

include hP in
theorem exactAt (hs : Ideal.span (Set.range s) = ⊤) (n : ℕ) (hn : n ≠ 0) :
    (Cech.SectionsExactness.CechSectionsExactness.sections R (Spec (CommRingCat.of R))
      (fun i => IntersectionLocalization.AffineIntersectionLocalization.principal R (s i)) P ⊤).ExactAt n := by
  have : ∀ i n, IsLocalizedModule (Submonoid.powers (s i))
      ((Cech.SectionsExactness.CechSectionsExactness.restriction R (Spec (CommRingCat.of R))
        (fun j => IntersectionLocalization.AffineIntersectionLocalization.principal R (s j)) P (IntersectionLocalization.AffineIntersectionLocalization.principal R (s i))).f n).hom :=
    cochain_localization R s P hP
  exact Cech.SectionsExactness.CechSectionsExactness.global_exactAt R (Spec (CommRingCat.of R))
    (fun i => IntersectionLocalization.AffineIntersectionLocalization.principal R (s i)) P s hs n hn

theorem tilde_exactAt (M : ModuleCat.{u} R) (hs : Ideal.span (Set.range s) = ⊤)
    (n : ℕ) (hn : n ≠ 0) :
    (Cech.SectionsExactness.CechSectionsExactness.sections R (Spec (CommRingCat.of R))
      (fun i => IntersectionLocalization.AffineIntersectionLocalization.principal R (s i))
      (modulesSpecToSheaf.obj (tilde (R := CommRingCat.of R) M)).obj ⊤).ExactAt n :=
  exactAt R s _ (isLocalizing_tilde (R := CommRingCat.of R) M) hs n hn

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.CechExactness.AffineCechExactness
