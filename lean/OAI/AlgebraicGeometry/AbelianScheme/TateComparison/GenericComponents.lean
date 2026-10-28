import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeEndPoints
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coproduct

/-! # Generic Components -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The arithmetic component decomposition gives an actual disjoint
union presentation over K, with its original component inclusions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

def Data.SphericalPELAlbaneseData.genericComponentAssembly : OverCoproduct.overCoproduct D.componentGeneric ⟶ D.space :=
  OverCoproduct.overCoproductDesc D.componentGeneric D.componentInclusion

include hg in
theorem Data.SphericalPELAlbaneseData.genericComponentAssembly_isIso : IsIso D.genericComponentAssembly := by
  have : IsIso D.componentAssembly := hg.decomposition
  let e := asIso D.componentAssembly
  have he (j : Fin D.componentCount) : Sigma.ι D.components.S j ≫ e.hom = D.inclusion j := by
    simp only [e, asIso_hom, Data.SphericalPELAlbaneseData.componentAssembly, Sigma.ι_comp_desc]
  have hi (j : Fin D.componentCount) : IsOpenImmersion (D.componentInclusion j).left := by
    have : IsOpenImmersion (D.inclusion j).left :=
      he j ▸ PELModuli.IntegralModel.Coproduct.decomposition_inclusion_open D.components.S e j
    exact PELModuli.IntegralModel.Coproduct.baseChange_inclusion_open D.generic (D.inclusion j)
  have hc (x : D.space.left) : ∃ j, x ∈ Set.range (D.componentInclusion j).left := by
    simpa only [he] using PELModuli.IntegralModel.Coproduct.baseChange_decomposition_cover D.components.S D.generic e x
  have hd : Pairwise (fun i j => Disjoint (Set.range (D.componentInclusion i).left)
      (Set.range (D.componentInclusion j).left)) := by
    simpa only [he] using PELModuli.IntegralModel.Coproduct.baseChange_decomposition_disjoint D.components.S D.generic e
  have : IsIso D.genericComponentAssembly.left := by
    change IsIso (Sigma.desc (fun j => (D.componentInclusion j).left))
    apply (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
      (Cofan.mk D.space.left (fun j => (D.componentInclusion j).left))).mp
    apply nonempty_isColimit_cofanMk_of
    · apply top_unique
      intro x _
      obtain ⟨j, hj⟩ := hc x
      exact (Opens.mem_iSup).mpr ⟨j, hj⟩
    · intro i j hij
      change Disjoint (D.componentInclusion i).left.opensRange (D.componentInclusion j).left.opensRange
      rw [disjoint_iff]
      apply le_bot_iff.mp
      intro x hx
      exact (Set.disjoint_left.mp (hd hij)) hx.1 hx.2
  have : IsIso ((Over.forget (Spec (.of K))).map D.genericComponentAssembly) :=
    inferInstanceAs (IsIso D.genericComponentAssembly.left)
  exact isIso_of_reflects_iso D.genericComponentAssembly (Over.forget _)

def Data.SphericalPELAlbaneseData.genericComponentIso : OverCoproduct.overCoproduct D.componentGeneric ≅ D.space :=
  letI := D.genericComponentAssembly_isIso hg
  asIso D.genericComponentAssembly

theorem Data.SphericalPELAlbaneseData.genericComponentIso_ι (j : Fin D.componentCount) :
    OverCoproduct.overCoproductι D.componentGeneric j ≫ (D.genericComponentIso hg).hom = D.componentInclusion j :=
  OverCoproduct.overCoproductι_desc D.componentGeneric D.componentInclusion j

def Data.SphericalPELAlbaneseData.genericComponentBasePoint (j : Fin D.componentCount) :
    𝟙_ (Over (Spec (.of K))) ⟶ D.componentGeneric j :=
  (Functor.Monoidal.εIso (Over.pullback D.generic)).hom ≫ (Over.pullback D.generic).map (D.components.x₀ j)

include hg in
theorem Data.SphericalPELAlbaneseData.genericComponent_preconnected (j : Fin D.componentCount) :
    PreconnectedSpace (D.componentGeneric j).left := by
  have : GeometricallyConnected (D.components.S j).hom := (hg.componentGeometry j).2.2.2
  have : GeometricallyConnected (D.componentGeneric j).hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd (D.components.S j).hom D.generic))
  exact (GeometricallyConnected.connectedSpace_of_subsingleton (D.componentGeneric j).hom).toPreconnectedSpace

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
