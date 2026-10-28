import OAI.AlgebraicGeometry.Resolution.Blowups.Integral.OpenIdealSupport

/-! # Zero Or Unit Ideal -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Locally.ZeroOrUnitIdeal.Construction

noncomputable section

/-! Pointed open charts on which an ideal is zero or a unit detect its global dichotomy on an integral scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem idealSheaf_support_isOpen_of_pointed_zero_or_unit_charts
    {X : Scheme} (I : X.IdealSheafData)
    (hlocal : ∀ x : X, ∃ (V : Scheme) (j : V ⟶ X), IsOpenImmersion j ∧
      ∃ y : V, j y = x ∧ (I.comap j = ⊥ ∨ I.comap j = ⊤)) : IsOpen (I.support : Set X) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨V, j, hj, y, hy, hzero | htop⟩ := hlocal x
  · let : IsOpenImmersion j := hj
    refine ⟨Set.range j, ?_, j.isOpenEmbedding.isOpen_range, ⟨y, hy⟩⟩
    rintro _ ⟨z, rfl⟩
    have hz : z ∈ (I.comap j).support := by rw [hzero]; trivial
    rw [Scheme.IdealSheafData.support_comap] at hz
    exact hz
  · have hyI : y ∈ (I.comap j).support := by
      rw [Scheme.IdealSheafData.support_comap]
      change j y ∈ I.support
      rwa [hy]
    rw [htop, Scheme.IdealSheafData.support_top] at hyI
    exact False.elim hyI

theorem idealSheaf_eq_bot_or_top_of_pointed_zero_or_unit_charts
    {X : Scheme} [IsIntegral X] (I : X.IdealSheafData)
    (hlocal : ∀ x : X, ∃ (V : Scheme) (j : V ⟶ X), IsOpenImmersion j ∧
      ∃ y : V, j y = x ∧ (I.comap j = ⊥ ∨ I.comap j = ⊤)) : I = ⊥ ∨ I = ⊤ :=
  Integral.OpenIdealSupport.Construction.idealSheaf_eq_bot_or_top_of_isOpen_support I (idealSheaf_support_isOpen_of_pointed_zero_or_unit_charts I hlocal)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Locally.ZeroOrUnitIdeal.Construction
