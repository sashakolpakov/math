import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.AugmentationRestriction
import OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizedComplex
import Mathlib.Algebra.Homology.SingleHomology

/-! # Sections Exactness -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.SectionsExactness.CechSectionsExactness

noncomputable section

/-!
# Exactness of Čech sections from principal localization

Sections of the actual Čech presheaf complex contract over each cover
member. If restriction to these members localizes every cochain module,
the unit-ideal criterion gives exactness of global cochains.
-/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] (X : Scheme.{u})
  {ι : Type u} (U : ι → X.Opens) (P : Presheaf.CechPresheaf.Presheaves R X)

def sections (V : X.Opens) : CochainComplex (ModuleCat.{u} R) ℕ :=
  (((evaluation X.Opensᵒᵖ (ModuleCat.{u} R)).obj (op V)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (Presheaf.CechPresheaf.complex R X U P)

def restriction (V : X.Opens) : sections R X U P ⊤ ⟶ sections R X U P V :=
  (((evaluation X.Opensᵒᵖ (ModuleCat.{u} R)).map (homOfLE le_top : V ⟶ ⊤).op).mapHomologicalComplex
    (ComplexShape.up ℕ)).app (Presheaf.CechPresheaf.complex R X U P)

theorem member_exactAt (i : ι) (n : ℕ) (hn : n ≠ 0) :
    (sections R X U P (U i)).ExactAt n := by
  let G := Cover.CechRestriction.restrictionFunctor R (U i).ι
  let E := (evaluation (U i).toScheme.Opensᵒᵖ (ModuleCat.{u} R)).obj (op ⊤)
  let e := E.mapHomotopyEquiv (AugmentationRestriction.CechAugmentationRestriction.restrictedHomotopyEquiv R P U i)
  have hz : IsZero (((E.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((CochainComplex.single₀ (Presheaf.CechPresheaf.Presheaves R X)).obj P))).homology n) := by
    apply HomologicalComplex.ExactAt.isZero_homology
    apply HomologicalComplex.ExactAt.of_isZero
    exact E.map_isZero (G.map_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 P n hn))
  have ht := (hz.of_iso (e.toHomologyIso n).symm)
  have he := (HomologicalComplex.exactAt_iff_isZero_homology _ n).mpr ht
  change (sections R X U P ((U i).ι ''ᵁ ⊤)).ExactAt n at he
  rwa [Scheme.Opens.ι_image_top] at he

theorem global_exactAt (s : ι → R) (hs : Ideal.span (Set.range s) = ⊤)
    [∀ i n, IsLocalizedModule (Submonoid.powers (s i))
      ((restriction R X U P (U i)).f n).hom]
    (n : ℕ) (hn : n ≠ 0) : (sections R X U P ⊤).ExactAt n :=
  LocalizedComplex.LocalizedComplexExactness.exactAt R ι s hs (ComplexShape.up ℕ)
    (sections R X U P ⊤) (fun i => sections R X U P (U i))
    (fun i => restriction R X U P (U i)) n (fun i => member_exactAt R X U P i n hn)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.SectionsExactness.CechSectionsExactness
