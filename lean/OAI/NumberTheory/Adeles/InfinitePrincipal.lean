import OAI.NumberTheory.Adeles.InfiniteNorm
import OAI.NumberTheory.Adeles.NormAlgebra

/-! # Infinite Principal -/

namespace OAI.NumberTheory.Adeles.InfinitePrincipal.CompletionFactors

noncomputable section

/-! The local-to-global norm identity at the infinite places. -/

open _root_.NumberField
open scoped _root_.NumberField _root_.Topology TensorProduct _root_.NumberField.LiesOver

variable {F E : Type*} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E]

theorem infiniteNormCoordinate_principal (v : InfinitePlace F) (x : E) :
    InfiniteNorm.CompletionFactors.infiniteNormCoordinate v (algebraMap E (InfiniteAdeleRing E) x) =
      algebraMap F v.Completion (Algebra.norm F x) := by
  let : ∀ w : InfiniteNorm.CompletionFactors.InfinitePlacesOver E v, FiniteDimensional v.Completion w.val.Completion :=
    fun w => LocalNorms.CompletionFactors.infiniteCompletion_finiteDimensional v w.val
  have hn := NormAlgebra.CompletionFactors.norm_baseChange (R := F) (A := v.Completion) x
  rw [← Algebra.norm_eq_of_algEquiv (InfiniteNorm.CompletionFactors.infiniteTensorEquiv (E := E) v) (1 ⊗ₜ[F] x), NormAlgebra.CompletionFactors.norm_pi] at hn
  simpa [InfiniteNorm.CompletionFactors.infiniteTensorEquiv, InfiniteNorm.CompletionFactors.infiniteTensorMap, Algebra.algHom,
    InfiniteNorm.CompletionFactors.infiniteNormCoordinate, LocalNorms.CompletionFactors.infiniteLocalNorm] using hn

theorem infiniteAdeleNorm_principal (x : E) :
    InfiniteNorm.CompletionFactors.infiniteAdeleNorm (algebraMap E (InfiniteAdeleRing E) x) =
      algebraMap F (InfiniteAdeleRing F) (Algebra.norm F x) :=
  funext fun v => infiniteNormCoordinate_principal v x

end

end OAI.NumberTheory.Adeles.InfinitePrincipal.CompletionFactors
