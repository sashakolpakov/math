import OAI.AlgebraicGeometry.Comparison.Betti.FlasqueBiproduct
import OAI.AlgebraicTopology.DeRham.Comparison.CechComplexAugmentation
import OAI.AlgebraicTopology.Cohomology.Singular.SheafQuasiIso

/-! # Section Sheafification -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SectionSheafification.Integration

noncomputable section

/-! The actual sheafification unit on sections of any complex of complex
module presheaves, with its cochain naturality. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

open OAI.AlgebraicTopology.DeRham.Comparison.CechComplexAugmentation OAI.AlgebraicTopology.Cohomology.Singular.SheafQuasiIso

variable {X : TopCat.{0}} (K : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{0} ℂ) ℕ) (U : Opens X)

def sectionSheafification : AlgebraicTopology.DeRham.Comparison.CechComplexAugmentation.presheafComplexSections U K ⟶
    (((FlasqueBiproduct.sections U).mapHomologicalComplex (.up ℕ)).obj (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex K)) where
  f n := (toSheafify (Opens.grothendieckTopology X) (K.X n)).app (op U)
  comm' i j _ :=
    (congrArg (fun f => f.app (op U))
      (toSheafify_naturality (Opens.grothendieckTopology X) (K.d i j))).symm

variable {K} {L : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{0} ℂ) ℕ}

theorem sectionSheafification_naturality (f : K ⟶ L) :
    (AlgebraicTopology.DeRham.Comparison.CechComplexAugmentation.presheafComplexSectionsFunctor U).map f ≫ sectionSheafification L U =
      sectionSheafification K U ≫
        ((FlasqueBiproduct.sections U).mapHomologicalComplex (.up ℕ)).map
          (((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).mapHomologicalComplex
            (.up ℕ)).map f) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact congrArg (fun g => g.app (op U))
    (toSheafify_naturality (Opens.grothendieckTopology X) (f.f n))

end

end OAI.AlgebraicGeometry.Comparison.Betti.SectionSheafification.Integration
