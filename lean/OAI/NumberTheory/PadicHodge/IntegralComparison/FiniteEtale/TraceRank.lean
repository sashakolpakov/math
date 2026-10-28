import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.SheafTraceDegree
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteFlatChartModule

/-! # Trace Rank -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TraceRank

noncomputable section

/-! On a connected target, the coefficient trace of one is the actual
finite-flat rank. Thus the native sheaf de Rham transfer has that rank
as its pullback composite, with no extra degree hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

section Affine

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f]
  [LocallyOfFinitePresentation f] [PreconnectedSpace Y]
  (U : Y.Opens) (hU : IsAffineOpen U)

local instance : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := ArithmeticGeometry.OrdinaryLocus.Openness.FiniteFlatChartModule.Construction.affinePreimageSectionAlgebra f U

variable [Module.Free Γ(Y, U) Γ(X, f ⁻¹ᵁ U)]

include hU in
theorem trace_one (y : Y) :
    Algebra.trace Γ(Y, U) Γ(X, f ⁻¹ᵁ U) 1 = (f.finrank y : Γ(Y, U)) := by
  classical
  nontriviality Γ(Y, U)
  let : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := ArithmeticGeometry.OrdinaryLocus.Openness.FiniteFlatChartModule.Construction.affinePreimageSectionModule_finite f U hU
  let t : PrimeSpectrum Γ(Y, U) := Classical.choice inferInstance
  have hr : Module.finrank Γ(Y, U) Γ(X, f ⁻¹ᵁ U) = f.finrank y :=
    ((congrFun (Module.rankAtStalk_eq_finrank_of_free
      (R := Γ(Y, U)) (M := Γ(X, f ⁻¹ᵁ U))) t).symm.trans
        (ArithmeticGeometry.OrdinaryLocus.Openness.FiniteFlatChartModule.Construction.affinePreimageSectionModule_rank f U hU t)).trans
          (f.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace _ _)
  simpa only [map_one, hr, nsmul_eq_mul, mul_one] using
    (Algebra.trace_algebraMap (R := Γ(Y, U)) (S := Γ(X, f ⁻¹ᵁ U)) (1 : Γ(Y, U)))

end Affine

open OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TraceBasis

variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsFinite f.left] [Etale f.left] [IsProper Y.hom] [Smooth Y.hom]
  [PreconnectedSpace Y.left]

theorem pullback_trace (y : Y.left) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo.DeRhamPullback.sheafDirectImage f ≫ DeRhamSheafTrace.trace R X Y f =
      f.left.finrank y • 𝟙 (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) := by
  apply SheafTraceDegree.DeRham.pullback_trace_of_degree
  intro i
  let : Algebra Γ(Y.left, TraceBasis.opens R X Y f i) Γ(X.left, f.left ⁻¹ᵁ TraceBasis.opens R X Y f i) :=
    ArithmeticGeometry.OrdinaryLocus.Openness.FiniteFlatChartModule.Construction.affinePreimageSectionAlgebra f.left (TraceBasis.opens R X Y f i)
  let : Module.Free Γ(Y.left, TraceBasis.opens R X Y f i) Γ(X.left, f.left ⁻¹ᵁ TraceBasis.opens R X Y f i) :=
    TraceBasis.sourceFree R X Y f i
  exact trace_one f.left (TraceBasis.opens R X Y f i) (Fact.out : IsAffineOpen (TraceBasis.opens R X Y f i)) y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TraceRank
