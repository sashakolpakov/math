import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.ConcentrationSingle

/-! # Concentration Local Recovery -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ConcentrationLocalRecovery

noncomputable section

/-! A comparison compatible with the two original concentration arrows
recovers the same global class from its supported local representative. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.ConcentrationSingle

universe u v w z
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{z} D]
  (F G : CochainComplex C ℕ ⥤ D) (K : CochainComplex C ℕ) (c : ℕ)
  [IsIso (F.map (CohomologyConcentration.projection K c))] [IsIso (F.map (CohomologyConcentration.inclusion K c))]
  [IsIso (G.map (CohomologyConcentration.projection K c))] [IsIso (G.map (CohomologyConcentration.inclusion K c))]
  (a : F.obj K ⟶ G.obj K)
  (b : F.obj (CohomologyConcentration.truncation K c) ⟶ G.obj (CohomologyConcentration.truncation K c))
  (d : F.obj ((single C (.up ℕ) c).obj (K.homology c)) ⟶
    G.obj ((single C (.up ℕ) c).obj (K.homology c)))
  (hp : F.map (CohomologyConcentration.projection K c) ≫ b = a ≫ G.map (CohomologyConcentration.projection K c))
  (hi : F.map (CohomologyConcentration.inclusion K c) ≫ b = d ≫ G.map (CohomologyConcentration.inclusion K c))

include b hp hi

theorem square : (Functor.ConcentrationSingle.iso F K c).hom ≫ d = a ≫ (Functor.ConcentrationSingle.iso G K c).hom := by
  have h := CohomologyConcentrationNaturality.inverse_square d b
    (asIso (F.map (CohomologyConcentration.inclusion K c))) (asIso (G.map (CohomologyConcentration.inclusion K c))) hi.symm
  dsimp only [Functor.ConcentrationSingle.iso, Iso.trans_hom, Iso.symm_hom, asIso_hom]
  rw [Category.assoc, ← h, ← Category.assoc, hp, Category.assoc]

theorem recover {A : D} (l : A ⟶ F.obj ((single C (.up ℕ) c).obj (K.homology c))) :
    (l ≫ (Functor.ConcentrationSingle.iso F K c).inv) ≫ a = (l ≫ d) ≫ (Functor.ConcentrationSingle.iso G K c).inv := by
  apply (cancel_mono (Functor.ConcentrationSingle.iso G K c).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← square F G K c a b d hp hi, ← Category.assoc (Functor.ConcentrationSingle.iso F K c).inv,
    Iso.inv_hom_id, Category.id_comp]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ConcentrationLocalRecovery
