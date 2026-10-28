import OAI.RepresentationTheory.Weil.UnitarySplitting.TestSpaceAnalysis

/-! # Coordinate Change -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.CoordinateChange.Construction

noncomputable section

/-! Continuous additive coordinate changes on the actual Bruhat space. -/

theorem schwartzBruhat_comp_addEquiv
    {F : Type} [NormedField F] {m n : ℕ}
    (e : Local.FunctionsMetaplectic.Construction.Position F m ≃ₜ+ Local.FunctionsMetaplectic.Construction.Position F n)
    {f : Local.FunctionsMetaplectic.Construction.Position F n → ℂ} (hf : f ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat F n) :
    f ∘ e ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat F m := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with hf | ⟨d, a, φ, rfl⟩
      · exact Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem
          (hf.1.comp_continuous e.continuous) (hf.2.comp_homeomorph e.toHomeomorph)
      · exact Local.FunctionsMetaplectic.Construction.schwartz_coordinate_mem (a.trans e.symm) φ
  | zero => exact (Local.FunctionsMetaplectic.Construction.schwartzBruhat F m).zero_mem
  | add f g _ _ hf hg => exact (Local.FunctionsMetaplectic.Construction.schwartzBruhat F m).add_mem hf hg
  | smul c f _ hf => exact (Local.FunctionsMetaplectic.Construction.schwartzBruhat F m).smul_mem c hf

def schwartzBruhat_coordinateEquiv
    {F : Type} [NormedField F] {m n : ℕ}
    (e : Local.FunctionsMetaplectic.Construction.Position F m ≃ₜ+ Local.FunctionsMetaplectic.Construction.Position F n) :
    Local.FunctionsMetaplectic.Construction.schwartzBruhat F n ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F m where
  toFun f := ⟨f.val ∘ e, schwartzBruhat_comp_addEquiv e f.property⟩
  invFun f := ⟨f.val ∘ e.symm, schwartzBruhat_comp_addEquiv e.symm f.property⟩
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.CoordinateChange.Construction
