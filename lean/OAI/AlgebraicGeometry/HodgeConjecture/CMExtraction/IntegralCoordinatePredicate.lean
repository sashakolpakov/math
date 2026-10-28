import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdelicCoordinateSplit

/-! # Integral Coordinate Predicate -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralCoordinatePredicate.TestTransport

noncomputable section

/-! Primewise integrality of an arbitrary specified coordinate family. -/

theorem integral_coordinate_predicate {J : Type*} {P : Prop} (z : J → AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles)
    (hP : P ↔ ∀ j, z j ∈ AbelianModuli.ReferenceFamily.AdelicData.integralFiniteAdeles) :
    P ↔ ∀ j (p : ℕ) [Fact p.Prime], ‖RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (z j)‖ ≤ 1 :=
  hP.trans (forall_congr' (fun j => AdelicCoordinateSplit.TestTransport.integralFiniteAdeles_padic_iff (z j)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralCoordinatePredicate.TestTransport
