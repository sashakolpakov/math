import OAI.AlgebraicGeometry.Comparison.Betti.Complex.SheafCohomology

/-! # Additive Constant Ext -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AdditiveConstantExt.Cech

noncomputable section

/-! Normalize actual additive sheaf cohomology to Ext from the unlifted constant integers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.TopologicalSpace

variable (X : TopCat.{0})

abbrev constantIntegers :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)

local instance : HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
  HasExt.standard _

def constantIntegerExtCohomologyEquiv
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) (n : ℕ) :
    Ext.{1} (constantIntegers X) F n ≃+ Sheaf.H.{0} F n :=
  (SheafCohomology.ExtLeft.Projective.extLeftIso
    (SheafCohomology.ConstantCoefficients.Projective.constantIntegerUliftIso X) F n).trans
    (SheafCohomology.ExtNaturality.Projective.extChangeUniverseAddEquiv _ _ n)

theorem constantIntegerExt_subsingleton
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) (n : ℕ)
    (hF : Subsingleton (Sheaf.H.{0} F n)) :
    Subsingleton (Ext.{1} (constantIntegers X) F n) := by
  have := hF
  exact (constantIntegerExtCohomologyEquiv X F n).injective.subsingleton

end

end OAI.AlgebraicGeometry.Comparison.Betti.AdditiveConstantExt.Cech
