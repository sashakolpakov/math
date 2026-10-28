import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialEndEvaluation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointEvaluation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.MappedNeighborFormula

/-! # Transported Special Equation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TransportedSpecialEquation.CM

noncomputable section

/-! A proved special-fiber map square transports the integral reduction
equation to the algebraic specialization acting on the original source.
The algebraic and pointwise operators are identified by the constructed
specialization data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialEndEvaluation.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialEndEvaluation.CM.TransportedSpecialization

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)
  (H : CommGrp (Over (NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase (ZMod q)))) (e : A.specialFiber.scheme ≅ H.X)
  [IsMonHom e.hom] (U : Over (NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase (ZMod q)))

theorem specialized_action (f : A.ExtendingEndomorphism) :
    PointEvaluation.CM.action H U (SpecialEndEvaluation.CM.TransportedSpecialization.algebraicSpecialization A H e f.generic) =
      PointSpecializationFormula.CM.Points.evaluateAt H U (SpecialEndEvaluation.CM.TransportedSpecialization.integralReduction A H e f) := by
  rw [← SpecialEndEvaluation.CM.TransportedSpecialization.integralReduction_identification A H e f]
  exact PointEvaluation.CM.action_integral H U (SpecialEndEvaluation.CM.TransportedSpecialization.integralReduction A H e f)

variable {X Y : Over (NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase (ZMod q))} (s : X ≅ Y)
  (a : X ⟶ A.specialFiber.scheme) (b : Y ⟶ H.X)
  (hs : a ≫ e.hom = s.hom ≫ b)

def Equation (f : A.ExtendingEndomorphism) (x y : U ⟶ X)
    (Nx Ny : Multiset (U ⟶ X)) : Prop :=
  PointEvaluation.CM.action H U (SpecialEndEvaluation.CM.TransportedSpecialization.algebraicSpecialization A H e f.generic)
    (Additive.ofMul ((x ≫ s.hom) ≫ b) - Additive.ofMul ((y ≫ s.hom) ≫ b)) =
    (Nx.map (fun z => Additive.ofMul ((z ≫ s.hom) ≫ b))).sum -
      (Ny.map (fun z => Additive.ofMul ((z ≫ s.hom) ≫ b))).sum

include hs in
theorem equation_from_integral (f : A.ExtendingEndomorphism) (x y : U ⟶ X)
    (Nx Ny : Multiset (U ⟶ X))
    (h : PointSpecializationFormula.CM.Points.evaluateAt (SpecialEndEvaluation.CM.TransportedSpecialization.specialGroup A) U (SpecialEndEvaluation.CM.specialIntegralEnd A f)
      (Additive.ofMul (x ≫ a) - Additive.ofMul (y ≫ a)) =
      (Nx.map (fun z => Additive.ofMul (z ≫ a))).sum -
        (Ny.map (fun z => Additive.ofMul (z ≫ a))).sum) :
    Equation A H e U s b f x y Nx Ny := by
  unfold Equation
  rw [specialized_action]
  exact MappedNeighborFormula.CM.mapped_neighbor_formula (SpecialEndEvaluation.CM.TransportedSpecialization.specialGroup A) H e U s a b hs
    (SpecialEndEvaluation.CM.specialIntegralEnd A f) x y Nx Ny h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TransportedSpecialEquation.CM
