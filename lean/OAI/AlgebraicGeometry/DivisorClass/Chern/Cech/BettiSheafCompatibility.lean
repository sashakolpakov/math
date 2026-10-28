import OAI.AlgebraicGeometry.DivisorClass.Chern.ArbitraryCechDescent
import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.DescentCohomology

/-! # Betti Sheaf Compatibility -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.BettiSheafCompatibility

noncomputable section

/-! The original Cech-to-singular map agrees with the actual native sheaf comparison. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)
  (hU : ∀ x : X, ∃ i, x ∈ U i)

include hU in
theorem cechCover_iSup_eq_top : ⨆ i, U i = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨i, hi⟩ := hU x
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

variable [MetrizableSpace X] [StronglyLocallyContractibleSpace X] [LocallyPathConnectedSpace X]

theorem rationalCechTwo_sheafClass_eq
    (k : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Rational.Cech.RationalCech.cechComplex (Obj.RationalCech.locallyConstantPresheaf X) U) 2) :
    Abelian.CechComparison.abelianCechToSheaf U (Rational.HolomorphicPeriod.rationalConstantAbelianSheaf X) (cechCover_iSup_eq_top U hU) 1
        (Intrinsic.DescentCohomology.rationalNativeCechClass U 1 k) =
      Rational.BettiCechSheafComparison.rationalBettiCechSheafEquiv X 1 (Obj.RationalCech.singularClassOfCechCocycle X U hU 2 k) := by
  obtain ⟨c, d, hc, hk⟩ := ArbitraryCechDescent.exists_singularDescent_for_cechCocycle U hU k
  rw [← hc]
  exact d.native_sheaf_class k hk (cechCover_iSup_eq_top U hU)

theorem rationalCechSheafClass_eq_betti (hcov : ⨆ i, U i = ⊤)
    (k : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Rational.Cech.RationalCech.cechComplex (Obj.RationalCech.locallyConstantPresheaf X) U) 2) :
    IntegralCechSheaf.rationalCechSheafClass (X := X) U hcov 1 k.val (Intrinsic.DescentCohomology.rationalCechCocycle_closed U 1 k) =
      Rational.BettiCechSheafComparison.rationalBettiCechSheafEquiv X 1 (Obj.RationalCech.singularClassOfCechCocycle X U hU 2 k) :=
  rationalCechTwo_sheafClass_eq U hU k

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.BettiSheafCompatibility
