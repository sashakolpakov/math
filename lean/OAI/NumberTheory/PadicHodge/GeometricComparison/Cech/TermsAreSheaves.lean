import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.IntersectionSheaf
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Terms Are Sheaves -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TermsAreSheaves.CechTermsAreSheaves

noncomputable section

/-! Every term of the actual Čech presheaf complex of a module sheaf is already a sheaf. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite Simplicial

universe u

variable (R : Type u) [CommRing R] (X : Scheme.{u})
  (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
  {ι : Type u} (U : ι → X.Opens)

def termSheaf (n : ℕ) : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) :=
  ∏ᶜ (fun t : Fin (n + 1) → ι =>
    ⟨AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersection R X F.obj (∏ᶜ (U ∘ t)),
      IntersectionSheaf.CechIntersectionSheaf.isSheaf R X F (∏ᶜ (U ∘ t))⟩)

def termIso (n : ℕ) : (termSheaf R X F U n).obj ≅ (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.complex R X U F.obj).X n :=
  PreservesProduct.iso (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (fun t : Fin (n + 1) → ι =>
      ⟨AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersection R X F.obj (∏ᶜ (U ∘ t)),
        IntersectionSheaf.CechIntersectionSheaf.isSheaf R X F (∏ᶜ (U ∘ t))⟩)

theorem isSheaf (n : ℕ) : Presheaf.IsSheaf (Opens.grothendieckTopology X)
    ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.complex R X U F.obj).X n) :=
  (Presheaf.isSheaf_of_iso_iff (termIso R X F U n)).mp (termSheaf R X F U n).property

theorem unit_isIso (n : ℕ) : IsIso (toSheafify (Opens.grothendieckTopology X)
    ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.complex R X U F.obj).X n)) :=
  isIso_toSheafify (Opens.grothendieckTopology X) (isSheaf R X F U n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TermsAreSheaves.CechTermsAreSheaves
