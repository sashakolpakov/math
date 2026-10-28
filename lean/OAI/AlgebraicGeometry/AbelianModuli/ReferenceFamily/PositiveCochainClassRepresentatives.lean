import OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology

/-! # Positive Cochain Class Representatives -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PositiveCochainClassRepresentatives

noncomputable section

/-! Every positive-degree native additive homology class is represented
by an actual closed cochain. -/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

theorem positiveCochainClass_surjective (K : CochainComplex AddCommGrpCat.{0} ℕ)
    (n : ℕ) (x : K.homology (n + 1)) :
    ∃ (s : K.X (n + 1)) (hs : K.d (n + 1) (n + 2) s = 0),
      K.homologyπ (n + 1) (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n K s hs) = x := by
  obtain ⟨c, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (K.homologyπ (n + 1))).mp inferInstance x
  have hs : K.d (n + 1) (n + 2) (K.iCycles (n + 1) c) = 0 :=
    ConcreteCategory.congr_hom (K.iCycles_d (n + 1) (n + 2)) c
  refine ⟨K.iCycles (n + 1) c, hs, congrArg (K.homologyπ (n + 1)) ?_⟩
  apply (AddCommGrpCat.mono_iff_injective (K.iCycles (n + 1))).mp inferInstance
  exact SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk n K _ hs

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PositiveCochainClassRepresentatives
