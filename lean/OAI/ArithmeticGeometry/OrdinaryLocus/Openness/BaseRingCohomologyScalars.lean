import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineCohomologyComparison
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseRingModuleSheaf
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechCoefficientMap
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-! # Base Ring Cohomology Scalars -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseRingCohomologyScalars.Construction

noncomputable section

/-! The actual affine-base scalar actions on sheaf cohomology and Cech cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (M : X.Modules)

@[reducible]
def baseRingSheafCohomologyModule (n : ℕ) : Module R (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H M n) := by
  letI := AlgebraicGeometry.SheafCohomology.AffineH.Projective.globalSectionsCohomologyModule M n
  exact Module.compHom (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H M n) (BaseRingModuleSheaf.Construction.baseRingConstants f)

theorem baseRingCech_globalSmulMap {ι : Type u} (U : ι → X.Opens) (r : R) :
    OpenCechCoefficientMap.Construction.openCechCoefficientMap ((BaseRingModuleSheaf.Construction.modulesAsBaseRingSheaf f).map
      (AlgebraicGeometry.SheafCohomology.AffineH.Projective.globalSmulHom M (BaseRingModuleSheaf.Construction.baseRingConstants f r))) U =
      r • 𝟙 (BaseRingModuleSheaf.Construction.schemeModuleCechShortComplex f M U) := by
  apply ShortComplex.Hom.ext
  · ext z
    funext i
    rfl
  · ext z
    funext i j
    rfl
  · ext z
    funext i j k
    rfl

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseRingCohomologyScalars.Construction
