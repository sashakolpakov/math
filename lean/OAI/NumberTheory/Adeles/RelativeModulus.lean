import OAI.NumberTheory.Adeles.RelativePrincipal
import OAI.NumberTheory.Adeles.FiniteCharacter

/-! # Relative Modulus -/

namespace OAI.NumberTheory.Adeles.RelativeModulus.CompletionFactors

noncomputable section

/-! Compatibility of the constructed relative norm with the absolute idele modulus. -/

open _root_.NumberField IsDedekindDomain HeightOneSpectrum
open scoped _root_.NumberField _root_.Topology NNReal OAI.NumberTheory.Adeles.LocalCompletions.CompletionFactors.FiniteLiesOver

variable {F E : Type*} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E]

theorem continuous_infiniteAdeleProductNorm (K : Type*) [Field K] [NumberField K] :
    Continuous (fun a : InfiniteAdeleRing K => ‖a‖) := by
  apply continuous_finsetProd
  intro v _
  exact (continuous_apply v).norm.pow v.mult

theorem infiniteAdeleProductNorm_relative (a : InfiniteAdeleRing E) :
    ‖InfiniteNorm.CompletionFactors.infiniteAdeleNorm (F := F) a‖ = ‖a‖ := by
  apply (InfiniteAdeleRing.denseRange_algebraMap E).induction_on
    (p := fun a => ‖InfiniteNorm.CompletionFactors.infiniteAdeleNorm (F := F) a‖ = ‖a‖) a
  · exact isClosed_eq
      ((continuous_infiniteAdeleProductNorm F).comp InfiniteNorm.CompletionFactors.continuous_infiniteAdeleNorm)
      (continuous_infiniteAdeleProductNorm E)
  · intro x
    rw [InfinitePrincipal.CompletionFactors.infiniteAdeleNorm_principal, InfiniteAdeleRing.coe_norm_eq_abs_norm,
      InfiniteAdeleRing.coe_norm_eq_abs_norm, Algebra.norm_norm]

theorem infiniteModulus_relative (a : (InfiniteAdeleRing E)ˣ) :
    LocalCompletions.CompletionFactors.infiniteModulus (InfiniteNorm.CompletionFactors.infiniteIdeleNorm (F := F) a) = LocalCompletions.CompletionFactors.infiniteModulus a := by
  apply NNReal.eq
  change ((∏ v : InfinitePlace F, ‖(InfiniteNorm.CompletionFactors.infiniteAdeleNorm a.val) v‖₊ ^ v.mult : ℝ≥0) : ℝ) =
    ((∏ w : InfinitePlace E, ‖a.val w‖₊ ^ w.mult : ℝ≥0) : ℝ)
  simp only [NNReal.coe_prod, NNReal.coe_pow, coe_nnnorm]
  exact infiniteAdeleProductNorm_relative a.val

theorem finiteModulus_relative_integral (a : (LocalCompletions.CompletionFactors.FiniteAdele E)ˣ)
    (ha : ∀ w : HeightOneSpectrum (𝓞 E), Valued.v (a.val w) = 1) :
    LocalCompletions.CompletionFactors.finiteModulus (FiniteNorm.CompletionFactors.finiteIdeleNorm (F := F) a) = 1 := by
  obtain ⟨hv, hi⟩ := FiniteCharacter.CompletionFactors.finiteIdele_integral_of_valuation_one a ha
  apply LocalCompletions.CompletionFactors.finiteModulus_eq_one_of_integral
  · intro v
    exact FiniteNorm.CompletionFactors.finiteNormCoordinate_integer v a.val (fun w => hv w.val)
  · intro v
    exact FiniteNorm.CompletionFactors.finiteNormCoordinate_integer v a.inv (fun w => hi w.val)

theorem finiteModulus_relative (hQuadratic : Module.finrank F E = 2) (a : (LocalCompletions.CompletionFactors.FiniteAdele E)ˣ) :
    LocalCompletions.CompletionFactors.finiteModulus (FiniteNorm.CompletionFactors.finiteIdeleNorm (F := F) a) = LocalCompletions.CompletionFactors.finiteModulus a := by
  refine FiniteCharacter.CompletionFactors.finiteCharacter_eq
    ((LocalCompletions.CompletionFactors.finiteModulus (K := F)).comp (FiniteNorm.CompletionFactors.finiteIdeleNorm (F := F) (E := E)).toMonoidHom)
    (LocalCompletions.CompletionFactors.finiteModulus (K := E)) ?_ ?_ ?_ a
  · exact finiteModulus_relative_integral (F := F)
  · intro u hu
    obtain ⟨hv, hi⟩ := FiniteCharacter.CompletionFactors.finiteIdele_integral_of_valuation_one u hu
    exact LocalCompletions.CompletionFactors.finiteModulus_eq_one_of_integral u hv hi
  · intro x
    have hp : FiniteNorm.CompletionFactors.finiteIdeleNorm (F := F) (FiniteCharacter.CompletionFactors.finitePrincipal x) =
        FiniteCharacter.CompletionFactors.finitePrincipal (Units.map (Algebra.norm F) x) := by
      apply Units.ext
      exact RelativePrincipal.CompletionFactors.finiteAdeleNorm_principal hQuadratic x.val
    change LocalCompletions.CompletionFactors.finiteModulus (FiniteNorm.CompletionFactors.finiteIdeleNorm (F := F) (FiniteCharacter.CompletionFactors.finitePrincipal x)) =
      LocalCompletions.CompletionFactors.finiteModulus (FiniteCharacter.CompletionFactors.finitePrincipal x)
    rw [hp]
    apply NNReal.eq
    change (LocalCompletions.CompletionFactors.finiteModulus (LocalCompletions.CompletionFactors.finiteIdeleProjection
      (LocalCompletions.CompletionFactors.principalIdele F (Units.map (Algebra.norm F) x))) : ℝ) =
        (LocalCompletions.CompletionFactors.finiteModulus (LocalCompletions.CompletionFactors.finiteIdeleProjection (LocalCompletions.CompletionFactors.principalIdele E x)) : ℝ)
    rw [LocalCompletions.CompletionFactors.finiteModulus_principal, LocalCompletions.CompletionFactors.finiteModulus_principal]
    simp only [Units.coe_map, Algebra.norm_norm]

theorem relativeIdeleNorm_modulus (hQuadratic : Module.finrank F E = 2) (a : LocalCompletions.CompletionFactors.Idele E) :
    LocalCompletions.CompletionFactors.ideleModulus (IdeleNorm.CompletionFactors.relativeIdeleNorm (F := F) a) = LocalCompletions.CompletionFactors.ideleModulus a := by
  apply Units.ext
  change LocalCompletions.CompletionFactors.infiniteModulus (InfiniteNorm.CompletionFactors.infiniteIdeleNorm (LocalCompletions.CompletionFactors.infiniteIdeleProjection a)) *
      LocalCompletions.CompletionFactors.finiteModulus (FiniteNorm.CompletionFactors.finiteIdeleNorm (LocalCompletions.CompletionFactors.finiteIdeleProjection a)) =
    LocalCompletions.CompletionFactors.infiniteModulus (LocalCompletions.CompletionFactors.infiniteIdeleProjection a) * LocalCompletions.CompletionFactors.finiteModulus (LocalCompletions.CompletionFactors.finiteIdeleProjection a)
  rw [infiniteModulus_relative, finiteModulus_relative hQuadratic]

theorem relativeIdeleClassNorm_modulus (hQuadratic : Module.finrank F E = 2)
    (c : LocalCompletions.CompletionFactors.IdeleClass E) :
    LocalCompletions.CompletionFactors.ideleClassModulus (RelativePrincipal.CompletionFactors.relativeIdeleClassNorm hQuadratic c) = LocalCompletions.CompletionFactors.ideleClassModulus c := by
  induction c using QuotientGroup.induction_on with
  | H a => exact relativeIdeleNorm_modulus hQuadratic a

theorem relativeIdeleClassNorm_kernel_subset_normOne (hQuadratic : Module.finrank F E = 2) :
    {c : LocalCompletions.CompletionFactors.IdeleClass E | RelativePrincipal.CompletionFactors.relativeIdeleClassNorm hQuadratic c = 1} ⊆
      {c : LocalCompletions.CompletionFactors.IdeleClass E | LocalCompletions.CompletionFactors.ideleClassModulus c = 1} := by
  intro c hc
  change LocalCompletions.CompletionFactors.ideleClassModulus c = 1
  rw [← relativeIdeleClassNorm_modulus hQuadratic, hc, map_one]

end

end OAI.NumberTheory.Adeles.RelativeModulus.CompletionFactors
