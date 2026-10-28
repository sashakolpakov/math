import OAI.NumberTheory.Adeles.CompletionFactorsFiniteTensor
import OAI.NumberTheory.Adeles.InfinitePrincipal
import OAI.NumberTheory.Adeles.IdeleNorm

/-! # Relative Principal -/

namespace OAI.NumberTheory.Adeles.RelativePrincipal.CompletionFactors

noncomputable section

/-! Compatibility with principal ideles and descent of the quadratic relative norm. -/

open _root_.NumberField IsDedekindDomain HeightOneSpectrum
open scoped _root_.NumberField _root_.Topology TensorProduct OAI.NumberTheory.Adeles.LocalCompletions.CompletionFactors.FiniteLiesOver Valued

variable {F E : Type*} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E]

theorem finiteNormCoordinate_principal (hQuadratic : Module.finrank F E = 2)
    (v : HeightOneSpectrum (𝓞 F)) (x : E) :
    FiniteNorm.CompletionFactors.finiteNormCoordinate v (algebraMap E (LocalCompletions.CompletionFactors.FiniteAdele E) x) =
      algebraMap F (v.adicCompletion F) (Algebra.norm F x) := by
  have hn := NormAlgebra.CompletionFactors.norm_baseChange (R := F) (A := v.adicCompletion F) x
  rw [← Algebra.norm_eq_of_algEquiv (CompletionFactorsFiniteTensor.finiteTensorEquivQuadratic v hQuadratic) (1 ⊗ₜ[F] x),
    NormAlgebra.CompletionFactors.norm_pi] at hn
  simp [CompletionFactorsFiniteTensor.finiteTensorEquivQuadratic, CompletionFactorsFiniteTensor.finiteTensorMap, CompletionFactorsFiniteTensor.finiteTensorMapAt, Algebra.algHom] at hn
  exact hn

theorem finiteAdeleNorm_principal (hQuadratic : Module.finrank F E = 2) (x : E) :
    FiniteNorm.CompletionFactors.finiteAdeleNorm (algebraMap E (LocalCompletions.CompletionFactors.FiniteAdele E) x) =
      algebraMap F (LocalCompletions.CompletionFactors.FiniteAdele F) (Algebra.norm F x) := by
  apply FiniteAdeleRing.ext
  intro v
  exact finiteNormCoordinate_principal hQuadratic v x

theorem relativeAdeleNorm_principal (hQuadratic : Module.finrank F E = 2) (x : E) :
    IdeleNorm.CompletionFactors.relativeAdeleNorm (algebraMap E (LocalCompletions.CompletionFactors.Adele E) x) =
      algebraMap F (LocalCompletions.CompletionFactors.Adele F) (Algebra.norm F x) :=
  Prod.ext (InfinitePrincipal.CompletionFactors.infiniteAdeleNorm_principal x) (finiteAdeleNorm_principal hQuadratic x)

theorem relativeIdeleNorm_principal (hQuadratic : Module.finrank F E = 2) (x : Eˣ) :
    IdeleNorm.CompletionFactors.relativeIdeleNorm (LocalCompletions.CompletionFactors.principalIdele E x) =
      LocalCompletions.CompletionFactors.principalIdele F (Units.map (Algebra.norm F) x) := by
  apply Units.ext
  exact relativeAdeleNorm_principal hQuadratic x.val

/-- The actual relative norm, descended from products of local field norms. -/
def relativeIdeleClassNorm (hQuadratic : Module.finrank F E = 2) :
    LocalCompletions.CompletionFactors.IdeleClass E →ₜ* LocalCompletions.CompletionFactors.IdeleClass F where
  toMonoidHom := QuotientGroup.lift (LocalCompletions.CompletionFactors.principalIdele E).range
    ((QuotientGroup.mk' (LocalCompletions.CompletionFactors.principalIdele F).range).comp IdeleNorm.CompletionFactors.relativeIdeleNorm.toMonoidHom) (by
      rintro a ⟨x, rfl⟩
      change QuotientGroup.mk (IdeleNorm.CompletionFactors.relativeIdeleNorm (LocalCompletions.CompletionFactors.principalIdele E x)) = 1
      rw [relativeIdeleNorm_principal hQuadratic]
      exact (QuotientGroup.eq_one_iff _).mpr ⟨Units.map (Algebra.norm F) x, rfl⟩)
  continuous_toFun := (QuotientGroup.isQuotientMap_mk (LocalCompletions.CompletionFactors.principalIdele E).range).continuous_iff.mpr
    (QuotientGroup.continuous_mk.comp IdeleNorm.CompletionFactors.relativeIdeleNorm.continuous)

@[simp] theorem relativeIdeleClassNorm_mk (hQuadratic : Module.finrank F E = 2)
    (a : LocalCompletions.CompletionFactors.Idele E) :
    relativeIdeleClassNorm hQuadratic (QuotientGroup.mk a) =
      QuotientGroup.mk (IdeleNorm.CompletionFactors.relativeIdeleNorm a) := rfl

end

end OAI.NumberTheory.Adeles.RelativePrincipal.CompletionFactors
