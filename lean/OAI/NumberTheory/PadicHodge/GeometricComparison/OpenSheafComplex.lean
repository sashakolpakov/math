import OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSheafOf
import Mathlib.Algebra.Homology.Additive

/-! # Open Sheaf Complex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSheafComplex.OpenSheafSectionComplex

noncomputable section

/-! Actual section complexes on an open chart agree with sections on its image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] {X Y : Scheme} (f : Y ⟶ X) [IsOpenImmersion f]
  (W : X.Opens) (hW : f ''ᵁ ⊤ = W)

abbrev sections (Z : Scheme) (U : Z.Opens) :
    Sheaf (Opens.grothendieckTopology Z) (ModuleCat R) ⥤ ModuleCat R :=
  sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op U)

def sectionIso : AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f ⋙ sections R Y ⊤ ≅ sections R X W :=
  NatIso.ofComponents (OpenSheafOf.OpenSheafSections.iso R f W hW)
    (fun {_ _} φ => (OpenSheafOf.OpenSheafSections.naturality R f W hW φ).symm)

def complexIso (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat R)) ℕ) :
    (((AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f ⋙ sections R Y ⊤).mapHomologicalComplex
      (.up ℕ)).obj K) ≅ (((sections R X W).mapHomologicalComplex (.up ℕ)).obj K) :=
  (NatIso.mapHomologicalComplex (sectionIso R f W hW) (.up ℕ)).app K

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSheafComplex.OpenSheafSectionComplex
