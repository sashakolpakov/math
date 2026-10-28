import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanRapid
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles

/-! # Archimedean Position Chart -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanPositionChart.Construction

noncomputable section

/-! The archimedean position product is identified with finite-dimensional
real Minkowski position space, preserving its supremum norm and rapid decay. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

open OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanRapid.LocalAnalysis

variable (F : Type) [Field F] [NumberField F]

omit [NumberField F] in
private theorem real_completion_embedding_norm (v : InfinitePlace F) (hv : v.IsReal) (x : v.Completion) :
    ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal hv x‖ = ‖x‖ := by
  simpa only [map_zero, dist_zero_right] using
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).dist_eq x 0

omit [NumberField F] in
private theorem complex_completion_embedding_norm (v : InfinitePlace F) (x : v.Completion) :
    ‖InfinitePlace.Completion.extensionEmbedding v x‖ = ‖x‖ := by
  simpa only [map_zero, dist_zero_right] using
    (InfinitePlace.Completion.isometry_extensionEmbedding v).dist_eq x 0

theorem infiniteAdeleMixedHomeomorph_norm (x : ∀ v : InfinitePlace F, v.Completion) :
    ‖ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F x‖ = ‖x‖ := by
  apply le_antisymm
  · change max ‖(fun v : {v : InfinitePlace F // v.IsReal} =>
        InfinitePlace.Completion.extensionEmbeddingOfIsReal v.property (x v))‖
      ‖(fun v : {v : InfinitePlace F // v.IsComplex} =>
        InfinitePlace.Completion.extensionEmbedding v.val (x v))‖ ≤ ‖x‖
    apply max_le
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
      intro v
      rw [real_completion_embedding_norm]
      exact norm_le_pi_norm x v.val
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
      intro v
      rw [complex_completion_embedding_norm]
      exact norm_le_pi_norm x v.val
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro v
    rcases v.isReal_or_isComplex with hv | hv
    · have h := norm_le_pi_norm (ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F x).1 ⟨v, hv⟩
      change ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal hv (x v)‖ ≤ _ at h
      rw [real_completion_embedding_norm] at h
      exact h.trans (le_max_left _ _)
    · have h := norm_le_pi_norm (ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F x).2 ⟨v, hv⟩
      change ‖InfinitePlace.Completion.extensionEmbedding v (x v)‖ ≤ _ at h
      rw [complex_completion_embedding_norm] at h
      exact h.trans (le_max_right _ _)

variable (N : ℕ)

def archimedeanPositionChart :
    (∀ v : InfinitePlace F, Local.FunctionsMetaplectic.Construction.Position v.Completion N) ≃ₜ (Fin N → mixedEmbedding.mixedSpace F) where
  toFun x i := ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F (fun v => x v i)
  invFun y v i := (ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F).symm (y i) v
  left_inv x := by
    funext v i
    exact congrFun ((ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F).symm_apply_apply (fun v => x v i)) v
  right_inv y := by
    funext i
    exact (ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F).apply_symm_apply (y i)
  continuous_toFun := continuous_pi (fun i => (ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F).continuous.comp
    (continuous_pi (fun v => (continuous_apply i).comp (continuous_apply v))))
  continuous_invFun := continuous_pi (fun v => continuous_pi (fun i =>
    (continuous_apply v).comp ((ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F).symm.continuous.comp (continuous_apply i))))

theorem archimedeanPositionChart_norm (x : ∀ v : InfinitePlace F, Local.FunctionsMetaplectic.Construction.Position v.Completion N) :
    ‖archimedeanPositionChart F N x‖ = ‖x‖ := by
  have hi (i : Fin N) : ‖archimedeanPositionChart F N x i‖ = ‖fun v => x v i‖ :=
    infiniteAdeleMixedHomeomorph_norm F _
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    intro i
    rw [hi]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    intro v
    exact (norm_le_pi_norm (x v) i).trans (norm_le_pi_norm x v)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro v
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    have h : ‖x v i‖ ≤ ‖fun w => x w i‖ := norm_le_pi_norm (fun w : InfinitePlace F => x w i) v
    rw [← hi] at h
    exact h.trans (norm_le_pi_norm (archimedeanPositionChart F N x) i)

def _root_.OAI.RepresentationTheory.Weil.AdelicSplitting.RestrictedTestFamilies.Construction.RestrictedTestFamily.mixedProductRapid (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    RapidFunctions.LocalAnalysis.RapidFunction (Fin N → mixedEmbedding.mixedSpace F) :=
  (f.archimedeanProductRapid F N).compNormPreserving (archimedeanPositionChart F N).symm
    (archimedeanPositionChart F N).symm.continuous (fun x => by
      have h := archimedeanPositionChart_norm F N ((archimedeanPositionChart F N).symm x)
      rw [(archimedeanPositionChart F N).apply_symm_apply] at h
      exact h.symm)

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanPositionChart.Construction
