import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.ConcentrationSingle

/-! # Concentration Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.ConcentrationMap

noncomputable section

/-! Naturality of the canonical concentration zigzag in the original
cochain complex, after a functor inverting its two maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z
open OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.ConcentrationSingle
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{z} D] (F : CochainComplex C ℕ ⥤ D)
  {K L : CochainComplex C ℕ} (a : K ⟶ L) (c : ℕ)
  [IsIso (F.map (CohomologyConcentration.projection K c))] [IsIso (F.map (CohomologyConcentration.inclusion K c))]
  [IsIso (F.map (CohomologyConcentration.projection L c))] [IsIso (F.map (CohomologyConcentration.inclusion L c))]

@[reassoc]
theorem naturality : F.map a ≫ (ConcentrationSingle.iso F L c).hom =
    (ConcentrationSingle.iso F K c).hom ≫ F.map ((single C (.up ℕ) c).map (homologyMap a c)) := by
  have hp := DualComplexHomology.map_square F _ _ _ _
    (πTruncGE_naturality a (CohomologyConcentration.shift c)).symm
  have hi := DualComplexHomology.map_square F _ _ _ _
    (CohomologyConcentrationNaturality.inclusion_naturality a c)
  have hi' := CohomologyConcentrationNaturality.inverse_square _ _
    (asIso (F.map (CohomologyConcentration.inclusion K c))) (asIso (F.map (CohomologyConcentration.inclusion L c))) hi
  simpa only [ConcentrationSingle.iso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    CohomologyConcentration.projection, Category.assoc] using
      DualComplexHomology.compose_squares _ _ _ _ _ _ _ hp hi'

end

universe u₁ v₁ w₁ z₁ a₁ b₁
open OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration
variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type w₁} [Category.{z₁} D] {E : Type a₁} [Category.{b₁} E]
  (F : CochainComplex C ℕ ⥤ D) (G : D ⥤ E)
  (K : CochainComplex C ℕ) (c : ℕ)
  [IsIso (F.map (CohomologyConcentration.projection K c))] [IsIso (F.map (CohomologyConcentration.inclusion K c))]

local instance mapped_projection : IsIso ((F ⋙ G).map (CohomologyConcentration.projection K c)) := by
  change IsIso (G.map (F.map (CohomologyConcentration.projection K c)))
  infer_instance
local instance mapped_inclusion : IsIso ((F ⋙ G).map (CohomologyConcentration.inclusion K c)) := by
  change IsIso (G.map (F.map (CohomologyConcentration.inclusion K c)))
  infer_instance

theorem iso_map : G.mapIso (ConcentrationSingle.iso F K c) =
    ConcentrationSingle.iso (F ⋙ G) K c := by
  apply Iso.ext
  simp only [Functor.mapIso_hom, ConcentrationSingle.iso,
    Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    Functor.map_comp, Functor.map_inv, Functor.comp_map]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.ConcentrationMap
