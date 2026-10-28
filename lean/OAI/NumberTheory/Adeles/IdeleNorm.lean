import OAI.NumberTheory.Adeles.FiniteNorm
import OAI.NumberTheory.Adeles.InfiniteNorm

/-! # Idele Norm -/

namespace OAI.NumberTheory.Adeles.IdeleNorm.CompletionFactors

noncomputable section

/-! The canonical relative norm on ideles, before quotienting by principal ideles. -/

open _root_.NumberField IsDedekindDomain HeightOneSpectrum
open scoped _root_.NumberField _root_.Topology OAI.NumberTheory.Adeles.LocalCompletions.CompletionFactors.FiniteLiesOver _root_.NumberField.LiesOver

variable {F E : Type*} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E]

def relativeAdeleNorm : LocalCompletions.CompletionFactors.Adele E →* LocalCompletions.CompletionFactors.Adele F :=
  MonoidHom.prodMap InfiniteNorm.CompletionFactors.infiniteAdeleNorm FiniteNorm.CompletionFactors.finiteAdeleNorm

theorem continuous_relativeAdeleNorm : Continuous (relativeAdeleNorm (F := F) (E := E)) :=
  InfiniteNorm.CompletionFactors.continuous_infiniteAdeleNorm.prodMap FiniteNorm.CompletionFactors.continuous_finiteAdeleNorm

/-- The product of the actual local extension norms, with the topology on adelic units. -/
def relativeIdeleNorm : LocalCompletions.CompletionFactors.Idele E →ₜ* LocalCompletions.CompletionFactors.Idele F where
  toMonoidHom := Units.map relativeAdeleNorm
  continuous_toFun := Continuous.units_map _ continuous_relativeAdeleNorm

@[simp] theorem relativeIdeleNorm_finite (a : LocalCompletions.CompletionFactors.Idele E) (v : HeightOneSpectrum (𝓞 F)) :
    (relativeIdeleNorm a).val.2 v =
      ∏ w : FiniteNorm.CompletionFactors.FinitePlacesOver E v, LocalNorms.CompletionFactors.finiteLocalNorm v w.val (a.val.2 w.val) := rfl

@[simp] theorem relativeIdeleNorm_infinite (a : LocalCompletions.CompletionFactors.Idele E) (v : InfinitePlace F) :
    (relativeIdeleNorm a).val.1 v =
      ∏ w : InfiniteNorm.CompletionFactors.InfinitePlacesOver E v, LocalNorms.CompletionFactors.infiniteLocalNorm v w.val (a.val.1 w.val) := rfl

end

end OAI.NumberTheory.Adeles.IdeleNorm.CompletionFactors
