import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.ZeroOrUnitIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.CarrierBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.CongruentMaps
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.ZeroCenter

/-! # Whole Or Empty Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Locally.WholeOrEmptyCenter.Construction

noncomputable section

/-! A center locally equal to an integral closed carrier or empty is globally that whole carrier or empty. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem idealSheaf_eq_or_top_of_pointed_whole_or_empty_charts
    {X : Scheme} (H C : X.IdealSheafData) [IsIntegral H.subscheme] (hHC : H ≤ C)
    (hlocal : ∀ x ∈ H.support, ∃ (V : Scheme) (j : V ⟶ X), IsOpenImmersion j ∧
      ∃ y : V, j y = x ∧ (C.comap j = H.comap j ∨ C.comap j = ⊤)) : C = H ∨ C = ⊤ := by
  have hcharts : ∀ x : H.subscheme, ∃ (V : Scheme) (j : V ⟶ H.subscheme), IsOpenImmersion j ∧
      ∃ y : V, j y = x ∧ ((C.comap H.subschemeι).comap j = ⊥ ∨ (C.comap H.subschemeι).comap j = ⊤) := by
    intro x
    have hx : H.subschemeι x ∈ H.support := by
      change H.subschemeι x ∈ (H.support : Set X)
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨x, rfl⟩
    obtain ⟨V, j, hj, y, hy, hC⟩ := hlocal (H.subschemeι x) hx
    let : IsOpenImmersion j := hj
    let K := H.comap j
    let k := IdealSheaf.CarrierBaseChange.Construction.idealSheafCarrierMapTo H K j rfl
    obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback
      (IdealSheaf.CarrierBaseChange.Construction.idealSheafCarrierMapTo_isPullback H K j rfl) x y hy.symm
    refine ⟨K.subscheme, k, inferInstance, z, hz, ?_⟩
    have he : (C.comap H.subschemeι).comap k = (C.comap j).comap K.subschemeι := by
      rw [← Scheme.IdealSheafData.comap_comp, IdealSheaf.CarrierBaseChange.Construction.idealSheafCarrierMapTo_over,
        Scheme.IdealSheafData.comap_comp]
    rw [he]
    rcases hC with hC | hC
    · left
      rw [hC]
      exact (GlobalCoefficient.ZeroCenter.Construction.idealSheaf_comap_subscheme_eq_bot_iff K K).mpr le_rfl
    · exact Or.inr (hC ▸ Scheme.IdealSheafData.comap_top K.subschemeι)
  rcases ZeroOrUnitIdeal.Construction.idealSheaf_eq_bot_or_top_of_pointed_zero_or_unit_charts (C.comap H.subschemeι) hcharts with hz | ht
  · left
    have he := congrArg (fun I => I.map H.subschemeι) hz
    rwa [IdealSheaf.CongruentMaps.Construction.idealSheaf_map_comap_subscheme_of_le H C hHC, Scheme.IdealSheafData.map_bot,
      Scheme.IdealSheafData.ker_subschemeι] at he
  · right
    have he := congrArg (fun I => I.map H.subschemeι) ht
    rwa [IdealSheaf.CongruentMaps.Construction.idealSheaf_map_comap_subscheme_of_le H C hHC, Scheme.IdealSheafData.map_top] at he

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Locally.WholeOrEmptyCenter.Construction
