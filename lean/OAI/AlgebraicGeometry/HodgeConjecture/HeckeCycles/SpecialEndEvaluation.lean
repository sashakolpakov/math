import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ExtendingPointAction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndTransport

/-! # Special End Evaluation -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialEndEvaluation.CM

/-! The endomorphism acting on reduced points is the actual GeometricComparison
specialization, under the established equivalence with algebraic ends. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ComparisonSpecialization.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NeronSpecialization.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ExtendingPointAction.CM

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)

def specialIntegralEnd (f : A.ExtendingEndomorphism) : AbelianScheme.TateComparison.End.IntegralEnd A.specialFiber.scheme :=
  AbelianScheme.TateComparison.BaseChange.endBaseChange (Geometric.ComparisonSpecialization.CM.integralGroup A).X
    (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q)) (ExtendingPointAction.CM.integralEnd A f)

theorem specializeEnd_eq_integralEquiv (f : A.ExtendingEndomorphism) :
    Geometric.ComparisonSpecialization.CM.specializeEnd A f.generic = EndomorphismComparison.CM.integralEquiv A.specialFiber.scheme (specialIntegralEnd A f) := by
  have h := congrArg
    (NeronSpecialization.CM.specialization (K := ℚ_[q]) (Geometric.ComparisonSpecialization.CM.integralGroup A)
      (PadicInt.toZMod : ℤ_[q] →+* ZMod q)) (Geometric.ComparisonSpecialization.CM.completedEnd_extending A f)
  have hs := h.trans (NeronSpecialization.CM.specialize_restriction (K := ℚ_[q]) (Geometric.ComparisonSpecialization.CM.integralGroup A)
    (PadicInt.toZMod : ℤ_[q] →+* ZMod q) (ExtendingPointAction.CM.integralEnd A f))
  exact congrArg (EndomorphismComparison.CM.integralEquiv A.specialFiber.scheme) hs

theorem specialIntegralEnd_eq (f : A.ExtendingEndomorphism) :
    specialIntegralEnd A f = (EndomorphismComparison.CM.integralEquiv A.specialFiber.scheme).symm
      (Geometric.ComparisonSpecialization.CM.specializeEnd A f.generic) := by
  apply (EndomorphismComparison.CM.integralEquiv A.specialFiber.scheme).injective
  exact (specializeEnd_eq_integralEquiv A f).symm.trans
    ((EndomorphismComparison.CM.integralEquiv A.specialFiber.scheme).apply_symm_apply _).symm

variable {S : Scheme} (G H : CommGrp (Over S)) (e : G.X ≅ H.X) [IsMonHom e.hom]

local instance : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)

theorem integralEquiv_transport (f : AbelianScheme.TateComparison.End.IntegralEnd G.X) :
    EndomorphismComparison.CM.integralEquiv H.X (EndTransportCM.CM.transport e f) =
      EndTransport.CM.schemeTransport G H e (EndomorphismComparison.CM.integralEquiv G.X f) := by
  apply Additive.toMul.injective
  apply Grp.hom_ext
  exact EndTransportCM.CM.transport_schemeMap e f

theorem inverseAlgebraicTransport (f : AbelianScheme.TateComparison.End.IntegralEnd G.X) :
    (EndTransport.CM.schemeTransport H G e.symm).symm
      (EndomorphismComparison.CM.integralEquiv G.X f) = EndomorphismComparison.CM.integralEquiv H.X (EndTransportCM.CM.transport e f) := by
  exact (integralEquiv_transport G H e f).symm

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialEndEvaluation.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialEndEvaluation.CM.TransportedSpecialization

/-! A generic comparison theorem identifies transport of the integral
reduction with transport of the same algebraic specialization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ComparisonSpecialization.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialEndEvaluation.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison.CM

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)
  (H : CommGrp (Over (NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase (ZMod q)))) (e : A.specialFiber.scheme ≅ H.X)
  [IsMonHom e.hom]

abbrev specialGroup : CommGrp (Over (NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase (ZMod q))) := CommGrp.mk A.specialFiber.scheme

local instance : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)

def algebraicSpecialization : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.variety.scheme →+* FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd H.X :=
  (EndTransport.CM.schemeTransport H (specialGroup A) e.symm).symm.toRingHom.comp
    (Geometric.ComparisonSpecialization.CM.specializeEnd A)

def integralReduction (f : A.ExtendingEndomorphism) : AbelianScheme.TateComparison.End.IntegralEnd H.X :=
  EndTransportCM.CM.transport e (specialIntegralEnd A f)

theorem integralReduction_identification (f : A.ExtendingEndomorphism) :
    EndomorphismComparison.CM.integralEquiv H.X (integralReduction A H e f) = algebraicSpecialization A H e f.generic := by
  have h := inverseAlgebraicTransport (specialGroup A) H e (specialIntegralEnd A f)
  have hs := congrArg
    (EndTransport.CM.schemeTransport H (specialGroup A) e.symm).symm
    (specializeEnd_eq_integralEquiv A f)
  exact h.symm.trans hs.symm

structure Data where
  specialization : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.variety.scheme →+* FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd H.X
  integralEnd : A.ExtendingEndomorphism → AbelianScheme.TateComparison.End.IntegralEnd H.X
  compatible : ∀ f, EndomorphismComparison.CM.integralEquiv H.X (integralEnd f) = specialization f.generic

def data : Data A H where
  specialization := algebraicSpecialization A H e
  integralEnd := integralReduction A H e
  compatible := integralReduction_identification A H e

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialEndEvaluation.CM.TransportedSpecialization

end

end OAI
