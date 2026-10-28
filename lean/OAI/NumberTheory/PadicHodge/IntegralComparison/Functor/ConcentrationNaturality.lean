import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.ConcentrationSingle

/-! # Concentration Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.ConcentrationNaturality

noncomputable section

/-! The original concentration zigzag commutes with natural maps
between cohomology functors, including restriction and forgetting support. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
universe u v w z
open OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.ConcentrationSingle
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{z} D]
  (F G : CochainComplex C ℕ ⥤ D) (τ : F ⟶ G)
  (K : CochainComplex C ℕ) (c : ℕ)
  [IsIso (F.map (CohomologyConcentration.projection K c))] [IsIso (F.map (CohomologyConcentration.inclusion K c))]
  [IsIso (G.map (CohomologyConcentration.projection K c))] [IsIso (G.map (CohomologyConcentration.inclusion K c))]

theorem square : (ConcentrationSingle.iso F K c).hom ≫ τ.app ((single C (.up ℕ) c).obj (K.homology c)) =
    τ.app K ≫ (ConcentrationSingle.iso G K c).hom := by
  have hi := CohomologyConcentrationNaturality.inverse_square
    (τ.app ((single C (.up ℕ) c).obj (K.homology c))) (τ.app (CohomologyConcentration.truncation K c))
    (asIso (F.map (CohomologyConcentration.inclusion K c))) (asIso (G.map (CohomologyConcentration.inclusion K c)))
    (τ.naturality (CohomologyConcentration.inclusion K c)).symm
  dsimp only [ConcentrationSingle.iso, Iso.trans_hom, Iso.symm_hom, asIso_hom]
  rw [Category.assoc, ← hi, ← Category.assoc, τ.naturality (CohomologyConcentration.projection K c), Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.ConcentrationNaturality
