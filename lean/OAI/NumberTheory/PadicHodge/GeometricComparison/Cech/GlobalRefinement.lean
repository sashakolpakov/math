import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.FamilyCoefficientNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.Refinement
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology

/-! # Global Refinement -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.GlobalRefinement.CechGlobalRefinement

noncomputable section

/-! The actual global-section identification of Čech presheaf cochains respects cover refinement. -/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {ι κ : Type u} (U : ι → X.left.Opens) (V : κ → X.left.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ U (r i)) (P : AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X.left)

theorem naturality :
    (((evaluation X.left.Opensᵒᵖ (ModuleCat.{u} R)).obj (op ⊤)).mapHomologicalComplex (.up ℕ)).map
        (Refinement.CechRefinement.map R X.left U V r hr P) ≫ (AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso.complexIso R X V P).hom =
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso.complexIso R X U P).hom ≫
        FamilyRefinement.CechFamilyRefinement.map (FormalCoproduct.mk ι U) (FormalCoproduct.mk κ V)
          (Refinement.CechRefinement.coverMap X.left U V r hr) P := by
  let E := (evaluation X.left.Opensᵒᵖ (ModuleCat.{u} R)).obj (op ⊤)
  let a := Refinement.CechRefinement.coverMap X.left U V r hr
  have h₁ := FamilyCoefficientNaturality.CechFamilyRefinement.coefficient_naturality E
    (FormalCoproduct.mk ι U) (FormalCoproduct.mk κ V) a (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersectionCoefficients R X.left P)
  have h₂ := (FamilyRefinement.CechFamilyRefinement.naturality (FormalCoproduct.mk ι U) (FormalCoproduct.mk κ V) a
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso.coefficientIso R X P).hom).symm
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.GlobalRefinement.CechGlobalRefinement
