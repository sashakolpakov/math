import OAI.AlgebraicGeometry.SheafCohomology.AffineComparison
import OAI.AlgebraicGeometry.SheafCohomology.AffineVanishing
import OAI.AlgebraicGeometry.SheafCohomology.FinitePresentation

/-! # Projective Affine Vanishing -/

namespace OAI.AlgebraicGeometry.SheafCohomology.ProjectiveAffineVanishing

noncomputable section

/-! Affine acyclicity for the actual complex cohomology used in ProjectiveCohomology. -/

open _root_.AlgebraicGeometry

/-- A quasicoherent module on an affine abelian variety has no positive-degree
cohomology. The comparison uses the same actual Zariski coefficient sheaf. -/
theorem coherentCohomology_vanish_of_isAffine
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) [IsAffine A.carrier]
    (M : A.carrier.Modules) [M.IsQuasicoherent] (n : ℕ) :
    Subsingleton (Sheaves.Projective.coherentCohomology A M (n + 1)) :=
  (AffineComparison.Projective.coherentCohomologyEquivZariski A M (n + 1)).subsingleton_congr.mpr
    (AffineVanishing.Projective.moduleAffineHSucc_subsingleton M n)

/-- Affine vanishing applies to the actual tensor-power sheaves of a line bundle. -/
theorem tensorPowerCohomology_vanish_of_isAffine
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) [IsAffine A.carrier]
    (L : Sheaves.Projective.LineBundle A) (m n : ℕ) :
    Subsingleton (Sheaves.Projective.coherentCohomology A (Sheaves.Projective.tensorPower A L m) (n + 1)) := by
  have : (Sheaves.Projective.tensorPower A L m).IsQuasicoherent :=
    (LineBundleLocalGenerators.Projective.lineBundleLocalGenerators A (TensorBundles.Projective.tensorPowerLineBundle A L m)).quasiCoherentData.isQuasicoherent
  exact coherentCohomology_vanish_of_isAffine A (Sheaves.Projective.tensorPower A L m) n

end

end OAI.AlgebraicGeometry.SheafCohomology.ProjectiveAffineVanishing
