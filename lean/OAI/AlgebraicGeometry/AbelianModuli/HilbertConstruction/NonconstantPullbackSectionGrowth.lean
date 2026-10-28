import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NonconstantMapSectionRatios
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PowerDimensionGrowth

/-! # Nonconstant Pullback Section Growth -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NonconstantPullbackSectionGrowth

noncomputable section

/-! Pulling the embedding bundle back along a nonconstant map from a proper integral scheme yields at least d+1 sections in every finite dth power section space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}} [IsIntegral X]
variable (p : X ⟶ Spec (.of K)) [UniversallyClosed p] (q : Y ⟶ Spec (.of K))
variable {L : Line.Bundles.LineBundle Y} (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L q)

theorem nonconstantMap_powerSections_dimension_lowerBound (f : X ⟶ Y)
    (hf : ¬ ∃ a : Spec (.of K) ⟶ Y, p ≫ a = f) (d : ℕ)
    [Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj ((E.power.pullback f).tensorPower d).sheaf)] :
    d + 1 ≤ Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj ((E.power.pullback f).tensorPower d).sheaf) := by
  obtain ⟨k, j, _, hx⟩ := NonconstantMapSectionRatios.nonconstantMap_exists_transcendentalSectionRatio p q E f hf
  exact @Section.PowerDimensionGrowth.sectionPower_dimension_lowerBound K _ X p (E.power.pullback f)
    (Ample.LineBundles.pullbackSection f (E.sections k)) (Ample.LineBundles.pullbackSection f (E.sections j))
    (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f (E.sections k))) le_rfl
    (Section.Frames.pullbackSection_nonvanishing_isIso (Ample.LineBundles.pullbackSection f (E.sections k))) hx d inferInstance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NonconstantPullbackSectionGrowth
