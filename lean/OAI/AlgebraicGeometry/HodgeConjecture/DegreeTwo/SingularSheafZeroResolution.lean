import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque
import OAI.AlgebraicTopology.Cohomology.Singular.StalkExactness

/-! # Singular Sheaf Zero Resolution -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions

noncomputable section

/-! The genuine rational singular sheaf complex resolves its degree-zero cohomology sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicTopology.Cohomology.Singular.StalkExactness

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) [StronglyLocallyContractibleSpace X]

abbrev rationalSingularSheafComplex :=
  AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X)

theorem rationalSingularSheaf_positive_exact (n : ℕ) :
    (rationalSingularSheafComplex X).ExactAt (n+1) := by
  apply (CycleClass.Geometric.GlobalSupportPurity.Cycles.rationalSheafComplex_exactAt_iff_stalk (rationalSingularSheafComplex X) (n+1)).mpr
  intro x
  exact (AlgebraicTopology.Cohomology.Singular.StalkExactness.singularStalkComplex_exactAt_succ (ModuleCat.of ℚ ℚ) X x n).of_iso
    (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafificationStalkComplexIso (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) x)

def rationalSingularSheafZeroAugmentation :
    (CochainComplex.single₀ _).obj ((rationalSingularSheafComplex X).homology 0) ⟶
      rationalSingularSheafComplex X :=
  ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation (rationalSingularSheafComplex X)

theorem rationalSingularSheafZeroAugmentation_quasiIso :
    QuasiIso (rationalSingularSheafZeroAugmentation X) :=
  ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation_quasiIso (rationalSingularSheafComplex X) (by
    intro n hn
    cases n with
    | zero => omega
    | succ n => exact (rationalSingularSheaf_positive_exact X n).isZero_homology)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions
