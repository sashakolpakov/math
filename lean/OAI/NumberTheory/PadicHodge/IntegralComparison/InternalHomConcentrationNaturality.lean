import OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomCechConcentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConcentratedNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomTotalNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConcentratedSerre

/-! # Internal Hom Concentration Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomConcentrationNaturality

noncomputable section

/-! The Serre comparison descends naturally to the actual surviving
cohomology sheaves of the internal Hom complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomCechTotal

variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (N : X.Modules) {K L : CochainComplex X.Modulesᵒᵖ ℕ}
  [∀ q, ((InternalHomCechTotal.internalComplex N K).X q).IsQuasicoherent]
  [∀ q, ((InternalHomCechTotal.internalComplex N L).X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → (InternalHomCechTotal.internalComplex N K).ExactAt q)
  (hL : ∀ q, q ≠ c → (InternalHomCechTotal.internalComplex N L).ExactAt q) (a : K ⟶ L)

def cohomologyMap (n : ℕ) :=
  (forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat).map
    (HomologicalComplex.homologyMap ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).map
      (HomologicalComplex.homologyMap (InternalHomTotalNaturality.internalMap N a) c)) n)

@[reassoc]
theorem total_naturality (n : ℕ) :
    HomologicalComplex.homologyMap (InternalHomTotalNaturality.totalMap π U N a) (n + c) ≫
        (InternalHomCechConcentration.totalHomologyIso π U hU N L c hL n).hom =
      (InternalHomCechConcentration.totalHomologyIso π U hU N K c hK n).hom ≫
        cohomologyMap π U N c a n := by
  let F := forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat
  let b := OrderedCech.QuasiIso.map π U (InternalHomTotalNaturality.internalMap N a)
  have hf : HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map b) (n + c) ≫
        (((InternalHomCechTotal.total π U N L).sc (n + c)).mapHomologyIso F).hom =
      (((InternalHomCechTotal.total π U N K).sc (n + c)).mapHomologyIso F).hom ≫
        F.map (HomologicalComplex.homologyMap b (n + c)) :=
    ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} Γ(S, ⊤)) (.up ℕ) (n + c)).map b) F
  have hc := DualComplexHomology.map_square F _ _ _ _
    (Cech.ConcentratedNaturality.naturality π U hU c hK hL
      (InternalHomTotalNaturality.internalMap N a) n)
  simpa only [InternalHomCechConcentration.totalHomologyIso, Iso.trans_hom,
    Functor.mapIso_hom, cohomologyMap, F, b, InternalHomTotalNaturality.totalMap] using
    DualComplexHomology.compose_squares _ _ _ _ _ _ _ hf hc

@[reassoc]
theorem serre_naturality (n : ℕ) {D₁ D₂ : AddCommGrpCat.{u}}
    (e₁ : InternalHomCechTotal.TotalIso π U N K (n + c) D₁) (e₂ : InternalHomCechTotal.TotalIso π U N L (n + c) D₂)
    (b : D₁ ⟶ D₂)
    (he : HomologicalComplex.homologyMap (InternalHomTotalNaturality.totalMap π U N a) (n + c) ≫
      e₂.hom = e₁.hom ≫ b) :
    cohomologyMap π U N c a n ≫ (ConcentratedSerre.Comparison.iso π U hU N L c hL n e₂).hom =
      (ConcentratedSerre.Comparison.iso π U hU N K c hK n e₁).hom ≫ b := by
  have hi := CohomologyConcentrationNaturality.inverse_square _ _
    (InternalHomCechConcentration.totalHomologyIso π U hU N K c hK n)
    (InternalHomCechConcentration.totalHomologyIso π U hU N L c hL n)
    (total_naturality π U hU N c hK hL a n)
  exact DualComplexHomology.compose_squares _ _ _ _ _ _ _ hi he

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomConcentrationNaturality
