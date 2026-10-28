import OAI.AlgebraicGeometry.SheafCohomology.ConstantCoefficients
import OAI.AlgebraicGeometry.SheafCohomology.ExtLeft
import OAI.AlgebraicGeometry.SheafCohomology.DimensionBound
import OAI.AlgebraicGeometry.SheafCohomology.VanishingGrothendieckVanishing

/-! # Coherent Vanishing -/

namespace OAI.AlgebraicGeometry.SheafCohomology.CoherentVanishing.Projective

noncomputable section

/-!
Grothendieck vanishing for the complex cohomology used by ProjectiveCohomology.
The change of coefficients is an equivalence of the actual Ext groups.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.TopologicalSpace

local instance (X : TopCat.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)) :=
  HasExt.standard _

local instance (X : TopCat.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℤ)) :=
  HasExt.standard _

/-- Forgetting complex coefficients identifies cohomology with abelian-sheaf cohomology. -/
def complexSheafCohomologyEquiv (X : TopCat.{0})
    (N : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)) (n : ℕ) :
    Ext.{1} ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).obj
      (ModuleCat.of ℂ ℂ)) N n ≃
      Sheaf.H.{0} ((IntegerCoefficients.Projective.integerSheafForget X).obj ((Coefficients.Projective.restrictComplexSheaf X).obj N)) n := by
  letI : HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
    HasExt.standard _
  let I := (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)
  let NAb := (IntegerCoefficients.Projective.integerSheafForget X).obj ((Coefficients.Projective.restrictComplexSheaf X).obj N)
  exact (ExtLeft.Projective.extLeftIso (ConstantCoefficients.Projective.extendConstantComplexIso X).symm N n).toEquiv |>.trans
    (Coefficients.Projective.complexSheafExtAdjunction X I N n).toEquiv |>.trans
    (IntegerCoefficients.Projective.integerSheafExtEquiv X I ((Coefficients.Projective.restrictComplexSheaf X).obj N) n).toEquiv |>.trans
    (ExtLeft.Projective.extLeftIso (ConstantCoefficients.Projective.forgetConstantIntegerIso X ≪≫ ConstantCoefficients.Projective.constantIntegerUliftIso X) NAb n).toEquiv
      |>.trans Ext.chgUniv

/-- Complex-sheaf cohomology vanishes above the topological Krull dimension. -/
theorem complexSheafVanishing (X : TopCat.{0}) [NoetherianSpace X]
    (N : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)) (n : ℕ)
    (h : (n : WithBot ℕ∞) > topologicalKrullDim X) :
    Subsingleton (Ext.{1}
      ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).obj
        (ModuleCat.of ℂ ℂ)) N n) :=
  (complexSheafCohomologyEquiv X N n).subsingleton_congr.mpr
    (VanishingGrothendieckVanishing.Projective.GrothendieckVanishing X n h
      ((IntegerCoefficients.Projective.integerSheafForget X).obj ((Coefficients.Projective.restrictComplexSheaf X).obj N)))

/-- The actual ProjectiveCohomology coherent cohomology vanishes above the Zariski Krull dimension. -/
theorem coherentCohomology_vanish_above_topologicalKrullDim
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (M : A.carrier.Modules) (n : ℕ)
    (h : (n : WithBot ℕ∞) > topologicalKrullDim A.carrier) :
    Subsingleton (Sheaves.Projective.coherentCohomology A M n) :=
  complexSheafVanishing (TopCat.of A.carrier) (Sheaves.Projective.complexSheaf A M) n h

/-- The vanishing bound uses the same geometric dimension as the ProjectiveCohomology statement. -/
theorem coherentCohomology_vanish_above_dimension
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (M : A.carrier.Modules) (n : ℕ)
    (h : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap < n) :
    Subsingleton (Sheaves.Projective.coherentCohomology A M n) := by
  apply coherentCohomology_vanish_above_topologicalKrullDim
  exact lt_of_le_of_lt
    (DimensionBound.Projective.topologicalKrullDim_le_schemeTranscendenceDimension A.variety.structureMap)
    (by exact_mod_cast h)

theorem coherentCohomology_finrank_eq_zero_above_dimension
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (M : A.carrier.Modules) (n : ℕ)
    (h : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap < n) :
    Module.finrank ℂ (Sheaves.Projective.coherentCohomology A M n) = 0 := by
  have := coherentCohomology_vanish_above_dimension A M n h
  exact Module.finrank_zero_of_subsingleton

end

end OAI.AlgebraicGeometry.SheafCohomology.CoherentVanishing.Projective
