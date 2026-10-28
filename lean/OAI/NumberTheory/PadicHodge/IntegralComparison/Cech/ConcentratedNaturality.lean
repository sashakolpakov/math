import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConcentratedCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConcentrationNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.SingleNaturality

/-! # Concentrated Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConcentratedNaturality

noncomputable section

/-! The complete comparison from a pure sheaf complex to the Čech
cohomology of its surviving cohomology sheaf is natural. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
  {K L : CochainComplex X.Modules ℕ}
  [∀ q, (K.X q).IsQuasicoherent] [∀ q, (L.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q) (hL : ∀ q, q ≠ c → L.ExactAt q)
  (a : K ⟶ L)

@[reassoc]
theorem naturality (n : ℕ) :
    HomologicalComplex.homologyMap (OrderedCech.QuasiIso.map π U a) (n + c) ≫
        (ConcentratedCohomology.iso π U hU L c hL n).hom =
      (ConcentratedCohomology.iso π U hU K c hK n).hom ≫
        HomologicalComplex.homologyMap ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).map
          (HomologicalComplex.homologyMap a c)) n := by
  have hc := ConcentrationNaturality.naturality π U hU c hK hL a (n + c)
  have hs := OrderedCech.SingleNaturality.homology_naturality π U
    (HomologicalComplex.homologyMap a c) c n
  simp only [ConcentrationNaturality.totalFunctor_map] at hc
  simpa only [ConcentratedCohomology.iso, Iso.trans_hom] using
    DualComplexHomology.compose_squares _ _ _ _ _ _ _ hc hs

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConcentratedNaturality
