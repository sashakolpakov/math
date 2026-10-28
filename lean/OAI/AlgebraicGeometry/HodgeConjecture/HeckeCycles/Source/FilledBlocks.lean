import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FilledLocal
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PairedPlaceFibers
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LinearMapEvaluation
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralBlockLattice

/-! # Filled Blocks -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FilledBlocks.CM

noncomputable section

/-! The filled source PEL operator has identity blocks in exactly the
distinguished conjugate pair and the original matrices in all other slots. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hb : P.b = B.b)
  {q : ℕ} [Fact q.Prime] (τ : Fin s × Bool → E →+* ℚ_[q])

def block (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (v : Fin s × Bool) : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q :=
  if v.1 = P.distinguished then 1 else Matrix.SpecialLinearGroup.map (τ v) g.val

theorem block_inv (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (v : Fin s × Bool) :
    block E P τ g⁻¹ v = (block E P τ g v)⁻¹ := by
  by_cases hv : v.1 = P.distinguished
  · simp only [block, ite_eq_left hv, inv_one]
  · simp only [block, ite_eq_right hv]
    exact map_inv (Matrix.SpecialLinearGroup.map (τ v)) g.val

theorem integral_iff (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    (∀ v, block E P τ g v ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) ↔
      ∀ v : Fin s × Bool, v.1 ≠ P.distinguished →
        Matrix.SpecialLinearGroup.map (τ v) g.val ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q :=
  CMExtraction.IntegralBlockLattice.TestTransport.identity_blocks_integral_iff (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q)
    (fun v : Fin s × Bool => v.1 = P.distinguished)
    (fun v => Matrix.SpecialLinearGroup.map (τ v) g.val)

variable (hinj : Function.Injective τ)
  (hconj : ∀ i b, τ (i, !b) = (τ (i, b)).comp (NumberField.IsCMField.complexConj E).toRingHom)

include hinj hconj in
theorem entry (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (v : Fin s × Bool) (i j : Fin 3) :
    CMExtraction.Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E (τ v)
      ((FilledLocal.CM.PEL.hom E Q P hb (τ (P.distinguished, false)) g).val (Pi.single j 1) i) =
        (block E P τ g v).val i j := by
  by_cases hv : v.1 = P.distinguished
  · have hp := (PairedPlaceFibers.CM.fiber E Q τ hinj hconj v (P.distinguished, false)).mpr hv
    exact (FilledLocal.CM.same E Q P hb (τ (P.distinguished, false)) (τ v) hp
      (RationalLocal.CM.finiteHom E Q g) i j).trans
      (by rw [block, ite_eq_left hv]; rfl)
  · have hp : QadicPlace.CM.place E (τ v) ≠
        QadicPlace.CM.place E (τ (P.distinguished, false)) :=
      fun h => hv ((PairedPlaceFibers.CM.fiber E Q τ hinj hconj v (P.distinguished, false)).mp h)
    exact (FilledLocal.CM.rational_other E Q P hb (τ (P.distinguished, false)) (τ v) hp g i j).trans
      (by rw [block, ite_eq_right hv]; rfl)

include hinj hconj in
theorem evaluate (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (v : Fin s × Bool)
    (x : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) :
    (fun i => CMExtraction.Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E (τ v)
      ((FilledLocal.CM.PEL.hom E Q P hb (τ (P.distinguished, false)) g).val x i)) =
      (block E P τ g v).val *ᵥ (fun i => CMExtraction.Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E (τ v) (x i)) := by
  have he := CMExtraction.LinearMapEvaluation.TestTransport.linearMap_evaluate (CMExtraction.Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E (τ v)).toRingHom
    (FilledLocal.CM.PEL.hom E Q P hb (τ (P.distinguished, false)) g).val.toLinearMap x
  have hm : (fun i j => CMExtraction.Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E (τ v)
      ((FilledLocal.CM.PEL.hom E Q P hb (τ (P.distinguished, false)) g).val (Pi.single j 1) i)) =
      (block E P τ g v).val := funext (fun i => funext (fun j => entry E Q P hb τ hinj hconj g v i j))
  exact he.trans (congrArg (fun M : Matrix (Fin 3) (Fin 3) ℚ_[q] =>
    M *ᵥ (fun i => CMExtraction.Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E (τ v) (x i))) hm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FilledBlocks.CM
