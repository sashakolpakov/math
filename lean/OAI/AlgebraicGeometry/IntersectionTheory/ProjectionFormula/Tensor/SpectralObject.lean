import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.Triangulated
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomologicalSpectralObject
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject
import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-! # Spectral Object -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.SpectralObject

noncomputable section

/-! The spectral object and spectral sequence of an actual filtered complex
after tensoring. Its relative terms are the homology of the total tensor
of the native relative mapping cones. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.ComposableArrows

variable (R : Type) [CommRing R] (K : CochainComplex (ModuleCat.{0} R) ℤ)
variable {ι : Type*} [Category* ι] (D : ι ⥤ CochainComplex (ModuleCat.{0} R) ℤ)

def triangulated : Triangulated.SpectralObject (HomotopyCategory (ModuleCat.{0} R) (.up ℤ)) ι :=
  ((HomotopyCategory.spectralObjectMappingCone (ModuleCat.{0} R)).precomp D).mapTriangulatedFunctor
    (Homotopy.homotopyFunctor R K)

def abelian : Abelian.SpectralObject (ModuleCat.{0} R) ι :=
  HomologicalSpectralObject.spectralObject (triangulated R K D)
    (HomotopyCategory.homologyFunctor (ModuleCat.{0} R) (.up ℤ) 0)

def termIso {i j : ι} (f : i ⟶ j) (n : ℤ) :
    ((abelian R K D).H n).obj (mk₁ f) ≅
      ((Homotopy.complexFunctor R K).obj (CochainComplex.mappingCone (D.map f))).homology n :=
  (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} R) (.up ℤ) n).app _

def spectralSequence (D : EInt ⥤ CochainComplex (ModuleCat.{0} R) ℤ) :
    E₂CohomologicalSpectralSequence (ModuleCat.{0} R) :=
  (abelian R K D).E₂SpectralSequence

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.SpectralObject
