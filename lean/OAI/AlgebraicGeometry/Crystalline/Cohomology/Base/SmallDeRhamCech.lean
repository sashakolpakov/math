import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoverReindex
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperCechRegularity
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.BaseCechHypercohomology

/-! # Small De Rham Cech -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech

noncomputable section

/-! The small coordinate cover computes the original proper de Rham cohomology, preserving finiteness and termwise regularity. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable (R : Type u) [CommRing R]
  (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] [Smooth X.hom]

def opens (i : SmallEtaleCover.BaseSmallEtaleCover.Index R X) : X.left.Opens :=
  (SmallEtaleCover.BaseSmallEtaleCover.opens R X i).val

local instance small_additive :
    (NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.complexFunctor (A := ModuleCat.{u} R) (opens R X)).Additive := by
  change (FormalCoproduct.cochainComplexFunctor (NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (opens R X))).Additive
  infer_instance

local instance original_additive :
    (NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.complexFunctor (A := ModuleCat.{u} R)
      (ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens R X)).Additive := by
  change (FormalCoproduct.cochainComplexFunctor
    (NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens R X))).Additive
  infer_instance

local instance reindexed_additive :
    (NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.complexFunctor (A := ModuleCat.{u} R)
      (ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens R X ∘
        (Fintype.equivFin (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index R X)).symm)).Additive := by
  change (FormalCoproduct.cochainComplexFunctor
    (NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens R X ∘
      (Fintype.equivFin (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index R X)).symm))).Additive
  infer_instance

def bicomplex : HomologicalComplex₂ (ModuleCat.{u} R) (.up ℕ) (.up ℕ) :=
  ((NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.complexFunctor (opens R X)).mapHomologicalComplex (.up ℕ)).obj
    (ProperDeRhamCechFiniteness.BaseSmoothProperDeRhamCechFiniteness.presheafComplex R X)

def total : CochainComplex (ModuleCat.{u} R) ℕ := (bicomplex R X).total (.up ℕ)

def originalBicomplexIso : ProperDeRhamCechFiniteness.BaseSmoothProperDeRhamCechFiniteness.bicomplex R X ≅ bicomplex R X :=
  (NatIso.mapHomologicalComplex (Cech.CoverReindex.CechCoverReindex.functorIso (A := ModuleCat.{u} R)
    (ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens R X)
    (Fintype.equivFin (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index R X)).symm) (.up ℕ)).app
      (ProperDeRhamCechFiniteness.BaseSmoothProperDeRhamCechFiniteness.presheafComplex R X)

def originalIso : ProperDeRhamCechFiniteness.BaseSmoothProperDeRhamCechFiniteness.total R X ≅ BaseSmallDeRhamCech.total R X :=
  HomologicalComplex₂.total.mapIso (originalBicomplexIso R X) (.up ℕ)

theorem finite [IsNoetherianRing R] (n : ℕ) : Module.Finite R ((BaseSmallDeRhamCech.total R X).homology n) := by
  let := ProperDeRhamCechFiniteness.BaseSmoothProperDeRhamCechFiniteness.finite R X n
  exact Module.Finite.equiv (HomologicalComplex.homologyMapIso (originalIso R X) n).toLinearEquiv

def originalEquiv [Module.Flat ℤ R] (n : ℕ) :
    (BaseSmallDeRhamCech.total R X).homology n ≃ₗ[R] DeRhamGlobalId.DeRhamGlobal.cohomology R X n :=
  (HomologicalComplex.homologyMapIso (originalIso R X).symm n).toLinearEquiv.trans
    (FlatBase.BaseCechHypercohomology.FlatBaseCechHypercohomology.properEquiv R X n)

theorem regular (n : ℕ) (r : R) (hr : r ∈ nonZeroDivisors R) :
    IsSMulRegular ((BaseSmallDeRhamCech.total R X).X n) r := by
  let e := ((HomologicalComplex.eval _ _ n).mapIso (originalIso R X).symm).toLinearEquiv
  intro x y hxy
  apply e.injective
  apply SmoothProperCechRegularity.BaseSmoothProperCechRegularity.total R X n r hr
  exact (e.map_smul r x).symm.trans ((congrArg e hxy).trans (e.map_smul r y))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech
