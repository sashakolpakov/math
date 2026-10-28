import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DualPurity

/-! # Dual Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DualCohomology

noncomputable section

/-! The actual ordinary dual Koszul complex has one cohomology module,
the original regular-sequence quotient. No coefficient injectivity is used. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (R : Type u) [CommRing R]

open OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DualPurity

abbrev ordinary (rs : List R) := DualComplexHomology.complex R (DualPurity.K R rs)

def comparison (rs : List R) (hreg : RingTheory.Sequence.IsWeaklyRegular R rs) :=
  Classical.choose (DualPurity.exists_comparison R rs hreg)

theorem comparison_quasiIso (rs : List R) (hreg : RingTheory.Sequence.IsWeaklyRegular R rs) :
    QuasiIso (comparison R rs hreg) :=
  Classical.choose_spec (DualPurity.exists_comparison R rs hreg)

def opHomologyIso (rs : List R) (hreg : RingTheory.Sequence.IsWeaklyRegular R rs) (i : ℤ) :
    op ((ordinary R rs).homology i) ≅
      ((DualPurity.single R).obj (op (DualPurity.Q R rs))).homology ((rs.length : ℤ) + i) := by
  have := comparison_quasiIso R rs hreg
  exact (((HomologicalComplex.homologyFunctor _ _ i).mapIso
      (DualFunctor.ordinaryDualIso R (DualPurity.K R rs))) ≪≫
        (ordinary R rs).homologyOp i).symm ≪≫
    (isoOfQuasiIsoAt (comparison R rs hreg) i).symm ≪≫
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R)ᵒᵖ (.up ℤ) 0).shiftIso
      (rs.length : ℤ) i ((rs.length : ℤ) + i) rfl).app ((DualPurity.single R).obj (op (DualPurity.Q R rs)))

theorem exactAt (rs : List R) (hreg : RingTheory.Sequence.IsWeaklyRegular R rs)
    (i : ℤ) (hi : i ≠ -(rs.length : ℤ)) : (ordinary R rs).ExactAt i := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hz := HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0
    (op (DualPurity.Q R rs)) ((rs.length : ℤ) + i) (by omega)
  exact ((opHomologyIso R rs hreg i).isZero_iff.mpr hz).unop

def homologyIso (rs : List R) (hreg : RingTheory.Sequence.IsWeaklyRegular R rs) :
    (ordinary R rs).homology (-(rs.length : ℤ)) ≅ DualPurity.Q R rs :=
  ((opHomologyIso R rs hreg (-(rs.length : ℤ)) ≪≫
    eqToIso (by rw [add_neg_cancel]) ≪≫
    HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (op (DualPurity.Q R rs))).unop).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DualCohomology
