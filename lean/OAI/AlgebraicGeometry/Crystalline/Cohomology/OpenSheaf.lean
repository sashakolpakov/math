import OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSheafOf
import Mathlib.Algebra.Homology.Additive

/-! # Open Sheaf -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.OpenSheaf.OpenSheafSectionComplex

noncomputable section

/-! Actual section complexes on an open chart agree with sections on its image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type u) [CommRing R] {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
  (W : X.Opens) (hW : f ''ᵁ ⊤ = W)

abbrev sections (Z : Scheme.{u}) (U : Z.Opens) :
    Sheaf (Opens.grothendieckTopology Z) (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
  sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op U)

def sectionIso : Cech.Cover.CechRestriction.sheafRestrictionFunctor R f ⋙ sections R Y ⊤ ≅ sections R X W :=
  NatIso.ofComponents (NumberTheory.PadicHodge.GeometricComparison.OpenSheafOf.OpenSheafSections.iso R f W hW)
    (fun {_ _} φ => (NumberTheory.PadicHodge.GeometricComparison.OpenSheafOf.OpenSheafSections.naturality R f W hW φ).symm)

def complexIso (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ) :
    (((Cech.Cover.CechRestriction.sheafRestrictionFunctor R f ⋙ sections R Y ⊤).mapHomologicalComplex
      (.up ℕ)).obj K) ≅ (((sections R X W).mapHomologicalComplex (.up ℕ)).obj K) :=
  (NatIso.mapHomologicalComplex (sectionIso R f W hW) (.up ℕ)).app K

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.OpenSheaf.OpenSheafSectionComplex
