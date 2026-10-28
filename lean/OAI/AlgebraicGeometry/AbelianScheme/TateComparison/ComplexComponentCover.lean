import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexAlbaneseCoordinates
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coproduct

/-! # Complex Component Cover -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The literal complex Albanese source inclusions form an open cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

include hg in
theorem Data.SphericalPELAlbaneseData.complexSourceInclusion_open (j : Fin D.componentCount) :
    IsOpenImmersion (D.complexSourceInclusion j).left := by
  have : IsIso D.componentAssembly := hg.decomposition
  have hi : Sigma.ι D.components.S j ≫ (asIso D.componentAssembly).hom = D.inclusion j := by
    simp only [asIso_hom, Data.SphericalPELAlbaneseData.componentAssembly, Sigma.ι_comp_desc]
  have : IsOpenImmersion (D.inclusion j).left :=
    hi ▸ PELModuli.IntegralModel.Coproduct.decomposition_inclusion_open D.components.S (asIso D.componentAssembly) j
  have : IsOpenImmersion (D.componentInclusion j).left :=
    PELModuli.IntegralModel.Coproduct.baseChange_inclusion_open D.generic (D.inclusion j)
  have : IsOpenImmersion ((Over.pullback D.complexGenericPoint).map (D.componentInclusion j)).left :=
    PELModuli.IntegralModel.Coproduct.baseChange_inclusion_open D.complexGenericPoint (D.componentInclusion j)
  let e := (Over.pullbackComp D.complexGenericPoint D.generic).app (D.components.S j)
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).map e.hom))
  change IsOpenImmersion (e.hom.left ≫
    ((Over.pullback D.complexGenericPoint).map (D.componentInclusion j)).left)
  infer_instance

include hg in
theorem Data.SphericalPELAlbaneseData.complexSourceInclusion_cover (x : D.complexSpace.left) :
    ∃ j, x ∈ Set.range (D.complexSourceInclusion j).left := by
  have : IsIso D.componentAssembly := hg.decomposition
  have hi (j : Fin D.componentCount) : Sigma.ι D.components.S j ≫
      (asIso D.componentAssembly).hom = D.inclusion j := by
    simp only [asIso_hom, Data.SphericalPELAlbaneseData.componentAssembly, Sigma.ι_comp_desc]
  obtain ⟨j, hj⟩ := PELModuli.IntegralModel.Coproduct.baseChange_decomposition_cover D.components.S D.generic
    (asIso D.componentAssembly) (pullback.fst D.space.hom D.complexGenericPoint x)
  simp only [hi] at hj
  have hx : x ∈ Set.range ((Over.pullback D.complexGenericPoint).map (D.componentInclusion j)).left := by
    rw [PELModuli.IntegralModel.Coproduct.baseChange_map_range]
    exact hj
  obtain ⟨z, hz⟩ := hx
  let e := (Over.pullbackComp D.complexGenericPoint D.generic).app (D.components.S j)
  refine ⟨j, e.inv.left z, ?_⟩
  have he : e.hom.left (e.inv.left z) = z := by
    exact congrArg (fun f => f z) (congrArg (fun f => f.left) e.inv_hom_id)
  change ((Over.pullback D.complexGenericPoint).map (D.componentInclusion j)).left
    (e.hom.left (e.inv.left z)) = x
  rw [he]
  exact hz

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
