import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mixed.SheafLocality
import Mathlib.Algebra.Homology.SingleHomology

/-! # Sheaf Exactness -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.SheafExactness.MixedCechSheafExactness

noncomputable section

/-!
Mixed-universe version for the native crystalline coefficient modules.

# Global exactness of Čech sheaves in positive degrees

Restrictions of the global Čech sheaf complex are contracted on every
cover member. Restriction preserves homology, and zero sheaves are
detected on an open cover. Consequently all its positive homology
sheaves vanish.
-/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry

universe u v

section General

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  (G : A ⥤ B) [G.Additive] [G.PreservesHomology]

def mapHomologyIso (K : CochainComplex A ℕ) (n : ℕ) :
    ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology n ≅ G.obj (K.homology n) :=
  (K.sc n).mapHomologyIso G

end General

section Single

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  (G : A ⥤ B) [G.Additive] (P : A) (n : ℕ) (hn : n ≠ 0)

include hn in
theorem mapped_single_homology_zero :
    IsZero (((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      ((CochainComplex.single₀ A).obj P)).homology n) :=
  (HomologicalComplex.ExactAt.of_isZero
    (G.map_isZero (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 P n hn))).isZero_homology

end Single

variable (R : Type v) [CommRing R] (X : Scheme.{u})
  {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤) (P : Presheaf.MixedCechPresheaf.Presheaves R X)

theorem restricted_homology_zero (i : ι) (n : ℕ) (hn : n ≠ 0) :
    IsZero ((CechRestriction.MixedCechRestriction.sheafRestrictionFunctor R (U i).ι).obj
      ((Presheaf.MixedCechPresheaf.sheafComplex R X U P).homology n)) := by
  let G := CechRestriction.MixedCechRestriction.sheafRestrictionFunctor R (U i).ι
  let F := Presheaf.MixedCechPresheaf.sheafification R (U i).toScheme
  let Q := Coefficients.MixedCechCoefficients.restricted X U i R P
  let e := CechRestriction.MixedCechRestriction.restrictedSheafHomotopyEquiv R P U i
  have hz := mapped_single_homology_zero F Q n hn
  have ht := hz.of_iso (e.toHomologyIso n).symm
  exact ht.of_iso (MixedCechSheafExactness.mapHomologyIso G (Presheaf.MixedCechPresheaf.sheafComplex R X U P) n).symm

include hU in
/-- The Čech sheaf complex of a covering family is exact in every positive degree. -/
theorem positive_homology_zero (n : ℕ) (hn : n ≠ 0) :
    IsZero ((Presheaf.MixedCechPresheaf.sheafComplex R X U P).homology n) :=
  Mixed.SheafLocality.MixedSheafLocality.isZero_of_restrictions R X U hU _ (fun i => restricted_homology_zero R X U P i n hn)

include hU in
theorem exactAt_positive (n : ℕ) (hn : n ≠ 0) : (Presheaf.MixedCechPresheaf.sheafComplex R X U P).ExactAt n :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ n).mpr (positive_homology_zero R X U hU P n hn)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.SheafExactness.MixedCechSheafExactness
