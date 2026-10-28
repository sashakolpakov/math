import OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.CechTerms

/-! # Cech Presheaf Sheaf -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.CechPresheafSheaf.LargeZariskiCechPresheafSheaf

noncomputable section

/-!
# The original Čech presheaf of a module sheaf is already a sheaf

Intersection coefficients are actual open direct images. Their products
are sheaves for arbitrary index families. The canonical sheafification
unit therefore identifies the whole original Čech presheaf complex
with the underlying Čech sheaf complex.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
  (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R))

local instance coefficientLimits : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

def intersectionSheaf (W : X.Opens) : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R) :=
  ⟨MixedCech.Presheaf.MixedCechPresheaf.intersection R X F.obj W,
    (Presheaf.isSheaf_of_iso_iff (CechTerms.LargeZariskiCechTerms.intersectionPresheafIso R X F W)).mp
      ((OpenPushforward.LargeZariskiOpenPushforward.intersection R W).obj F).property⟩

variable {ι : Type u} (U : ι → X.Opens)

theorem term_isSheaf (n : ℕ) : Presheaf.IsSheaf (Opens.grothendieckTopology X)
    (((MixedCech.Functor.MixedCechFunctor.functor R X U).obj F.obj).X n) := by
  let T := fun t : Fin (n + 1) → ι => intersectionSheaf R X F (∏ᶜ (U ∘ t))
  let e := PreservesProduct.iso (sheafToPresheaf (Opens.grothendieckTopology X)
    (ModuleCat.{u + 1} R)) T
  exact (Presheaf.isSheaf_of_iso_iff e).mp (∏ᶜ T).property

def unit : (MixedCech.Functor.MixedCechFunctor.functor R X U).obj F.obj ⟶
    ((sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj ((MixedCech.Functor.MixedCechFunctor.sheafFunctor R X U).obj F) where
  f n := toSheafify (Opens.grothendieckTopology X) (((MixedCech.Functor.MixedCechFunctor.functor R X U).obj F.obj).X n)
  comm' n m _ :=
    ((sheafificationAdjunction (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)).unit.naturality
      (((MixedCech.Functor.MixedCechFunctor.functor R X U).obj F.obj).d n m)).symm

instance unit_isIso : IsIso (LargeZariskiCechPresheafSheaf.unit R X F U) := by
  have (n : ℕ) : IsIso ((LargeZariskiCechPresheafSheaf.unit R X F U).f n) :=
    isIso_toSheafify (Opens.grothendieckTopology X) (term_isSheaf R X F U n)
  exact HomologicalComplex.Hom.isIso_of_components _

def iso := asIso (LargeZariskiCechPresheafSheaf.unit R X F U)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.CechPresheafSheaf.LargeZariskiCechPresheafSheaf
