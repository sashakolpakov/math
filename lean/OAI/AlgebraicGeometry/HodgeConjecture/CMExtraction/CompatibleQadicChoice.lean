import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Parameters
import OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalPadic
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap

/-! # Compatible Qadic Choice -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CompatibleQadicChoice.ParameterChoices

noncomputable section

section

/-! Construct a q-adic choice while preserving the already chosen complex
and local closure embeddings. Normality aligns any available embedding
of the arithmetic field with this exact local closure. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenCharacters.CM
open OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalPadic

variable {K : Type} [Field K] [NumberField K]

def fieldInChosenClosure (j : ParameterChoices.Qbar →+* ℂ) (κ : K →+* ℂ) : K →ₐ[ℚ] ParameterChoices.Qbar :=
  (HeckeCycles.ChosenCharacters.CM.chosenClosureEquiv j).symm.toAlgHom.comp
    (κ.toRatAlgHom.codRestrict HeckeCycles.Coefficients.CM.algebraicField.toSubalgebra
      (fun x => mem_algebraicClosure_iff.mpr
        ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom κ.toRatAlgHom)))

theorem fieldInChosenClosure_image (j : ParameterChoices.Qbar →+* ℂ) (κ : K →+* ℂ) (x : K) :
    j (fieldInChosenClosure j κ x) = κ x := HeckeCycles.ChosenCharacters.CM.chosenClosureEquiv_inverse j _

theorem fieldInChosenClosure_compatible (j : ParameterChoices.Qbar →+* ℂ) (κ : K →+* ℂ) :
    j.comp (fieldInChosenClosure j κ).toRingHom = κ := by
  ext x
  exact fieldInChosenClosure_image j κ x

variable {q : ℕ} [Fact q.Prime]

def compatiblePadicEmbedding [IsGalois ℚ K]
    (ψ : K →+* ParameterChoices.Qbar) (ι : ParameterChoices.Qbar →+* AlgebraicClosure ℚ_[q]) (f : K →+* ℚ_[q]) : K →+* ℚ_[q] :=
  f.comp (GaloisDiscrete.ParameterChoices.embeddingAutEquiv ((algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp f)
    (ι.comp ψ).toRatAlgHom).toRingHom

theorem compatiblePadicEmbedding_spec [IsGalois ℚ K]
    (ψ : K →+* ParameterChoices.Qbar) (ι : ParameterChoices.Qbar →+* AlgebraicClosure ℚ_[q]) (f : K →+* ℚ_[q]) :
    (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp (compatiblePadicEmbedding ψ ι f) = ι.comp ψ := by
  ext x
  exact GaloisDiscrete.ParameterChoices.embeddingAutEquiv_spec ((algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp f)
    (ι.comp ψ).toRatAlgHom x

def qadicChoiceInChosenClosure (κ : K →+* ℂ) (j : ParameterChoices.Qbar →+* ℂ)
    (ι : ParameterChoices.Qbar →+* AlgebraicClosure ℚ_[q]) (f : K →+* ℚ_[q])
    (hf : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp f =
      ι.comp (fieldInChosenClosure j κ).toRingHom) : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q where
  complexClosure := j
  fieldInClosure := (fieldInChosenClosure j κ).toRingHom
  complex_compatibility := fieldInChosenClosure_compatible j κ
  iota := ι
  prime := PELModuli.CMPoints.LocalPadic.embeddingPlace f
  liesOver := PELModuli.CMPoints.LocalPadic.embeddingPlace_liesOver f
  completion := PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv f
  completion_continuous := PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv_continuous f
  completion_inverse_continuous := PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv_symm_continuous f
  closure_compatibility := by rw [PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv_comp]; exact hf.symm
  integralEmbedding := PELModuli.CMPoints.LocalPadic.integersToPadicInt f
  integral_compatibility := by
    rw [PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv_comp]
    ext x
    exact PELModuli.CMPoints.LocalPadic.integersToPadicInt_coe f x

theorem qadicChoiceInChosenClosure_embedding (κ : K →+* ℂ) (j : ParameterChoices.Qbar →+* ℂ)
    (ι : ParameterChoices.Qbar →+* AlgebraicClosure ℚ_[q]) (f : K →+* ℚ_[q])
    (hf : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp f =
      ι.comp (fieldInChosenClosure j κ).toRingHom) :
    HeckeCycles.QadicModelMap.CM.localFieldEmbedding (qadicChoiceInChosenClosure κ j ι f hf) = f :=
  PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv_comp f

def normalFieldQadicChoice [IsGalois ℚ K] (κ : K →+* ℂ) (j : ParameterChoices.Qbar →+* ℂ)
    (ι : ParameterChoices.Qbar →+* AlgebraicClosure ℚ_[q]) (f : K →+* ℚ_[q]) : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q :=
  qadicChoiceInChosenClosure κ j ι
    (compatiblePadicEmbedding (fieldInChosenClosure j κ).toRingHom ι f)
    (compatiblePadicEmbedding_spec _ ι f)

theorem normalFieldQadicChoice_closures [IsGalois ℚ K] (κ : K →+* ℂ) (j : ParameterChoices.Qbar →+* ℂ)
    (ι : ParameterChoices.Qbar →+* AlgebraicClosure ℚ_[q]) (f : K →+* ℚ_[q]) :
    (normalFieldQadicChoice κ j ι f).complexClosure = j ∧
      (normalFieldQadicChoice κ j ι f).iota = ι := ⟨rfl, rfl⟩

end

section

/-! A prime chosen to split one normal field containing the arithmetic
base supplies the comparison place for every preselected closure embedding.
The arithmetic base itself need not be normal. -/

open OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalPadic

variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F]
  {q : ℕ} [Fact q.Prime]

def extendLocalFieldEmbedding (i : K →+* F) (g : K →+* AlgebraicClosure ℚ_[q]) :
    F →+* AlgebraicClosure ℚ_[q] := by
  let : Algebra K F := i.toAlgebra
  let : IsScalarTower ℚ K F := IsScalarTower.of_algebraMap_eq (fun r => by
    change (r : F) = i (r : K)
    simp)
  let : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  let : Algebra K (AlgebraicClosure ℚ_[q]) := g.toAlgebra
  exact (IsAlgClosed.lift : F →ₐ[K] AlgebraicClosure ℚ_[q]).toRingHom

theorem extendLocalFieldEmbedding_spec (i : K →+* F) (g : K →+* AlgebraicClosure ℚ_[q]) :
    (extendLocalFieldEmbedding i g).comp i = g := by
  let : Algebra K F := i.toAlgebra
  let : IsScalarTower ℚ K F := IsScalarTower.of_algebraMap_eq (fun r => by
    change (r : F) = i (r : K)
    simp)
  let : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  let : Algebra K (AlgebraicClosure ℚ_[q]) := g.toAlgebra
  ext x
  exact (IsAlgClosed.lift : F →ₐ[K] AlgebraicClosure ℚ_[q]).commutes x

def normalExtensionPadicEmbedding [IsGalois ℚ F]
    (i : K →+* F) (g : K →+* AlgebraicClosure ℚ_[q]) (f : F →+* ℚ_[q]) : K →+* ℚ_[q] :=
  (f.comp (GaloisDiscrete.ParameterChoices.embeddingAutEquiv ((algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp f)
    (extendLocalFieldEmbedding i g).toRatAlgHom).toRingHom).comp i

theorem normalExtensionPadicEmbedding_spec [IsGalois ℚ F]
    (i : K →+* F) (g : K →+* AlgebraicClosure ℚ_[q]) (f : F →+* ℚ_[q]) :
    (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp (normalExtensionPadicEmbedding i g f) = g := by
  ext x
  exact (GaloisDiscrete.ParameterChoices.embeddingAutEquiv_spec ((algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp f)
    (extendLocalFieldEmbedding i g).toRatAlgHom (i x)).trans
      (RingHom.congr_fun (extendLocalFieldEmbedding_spec i g) x)

def normalExtensionQadicChoice [IsGalois ℚ F]
    (κ : K →+* ℂ) (j : ParameterChoices.Qbar →+* ℂ) (ι : ParameterChoices.Qbar →+* AlgebraicClosure ℚ_[q])
    (i : K →+* F) (f : F →+* ℚ_[q]) : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q :=
  qadicChoiceInChosenClosure κ j ι
    (normalExtensionPadicEmbedding i (ι.comp (fieldInChosenClosure j κ).toRingHom) f)
    (normalExtensionPadicEmbedding_spec i _ f)

theorem exists_fixed_closure_qadicChoice_bound [IsGalois ℚ F]
    (κ : K →+* ℂ) (i : K →+* F) :
    ∃ d : ℕ, ∀ (q : ℕ) [Fact q.Prime], d < q → PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt F q →
      ∀ (j : ParameterChoices.Qbar →+* ℂ) (ι : ParameterChoices.Qbar →+* AlgebraicClosure ℚ_[q]),
      ∃ J : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q,
        J.complexClosure = j ∧ J.iota = ι ∧
          J.fieldInClosure = (fieldInChosenClosure j κ).toRingHom := by
  obtain ⟨d, hd⟩ := PELModuli.CMPoints.LocalPadic.exists_padic_embedding_bound F
  refine ⟨d, fun q _ hq hs j ι => ?_⟩
  obtain ⟨f⟩ := hd q hq hs
  exact ⟨normalExtensionQadicChoice κ j ι i f, rfl, rfl, rfl⟩

end

/-! The comparison place retains the exact complex embedding, native
closure valuation, and distinguished local embedding on E. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalPadic

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
  (hμ : D.reference.μ = E.val.toRingHom)
  (j : ParameterChoices.Qbar →+* ℂ) (ιE : E →ₐ[ℚ] ParameterChoices.Qbar) (hι : ∀ x : E, j (ιE x) = (x : ℂ))

include hg hμ hι in
theorem native_fieldInChosenClosure_restrict :
    (fieldInChosenClosure j D.complexEmbedding).toRingHom.comp D.fieldEmbedding = ιE.toRingHom := by
  ext x
  apply j.injective
  change j (fieldInChosenClosure j D.complexEmbedding (D.fieldEmbedding x)) = j (ιE x)
  rw [fieldInChosenClosure_image, hι]
  exact (RingHom.congr_fun hg.embedding x).trans (RingHom.congr_fun hμ x)

variable {F : Type} [Field F] [NumberField F] [IsGalois ℚ F]
  (i : K →+* F) (f : F →+* ℚ_[q])

def nativeQadicChoice : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q :=
  normalExtensionQadicChoice D.complexEmbedding j
    (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) i f

include hg hμ hι in
theorem nativeQadicChoice_local :
    (HeckeCycles.QadicModelMap.CM.localFieldEmbedding (nativeQadicChoice E D j ιE i f)).comp D.fieldEmbedding =
      LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false) := by
  let J := nativeQadicChoice E D j ιE i f
  have hJ := J.closure_compatibility
  have hE := native_fieldInChosenClosure_restrict E D hg hμ j ιE hι
  ext x
  apply (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).injective
  have h := RingHom.congr_fun hJ (D.fieldEmbedding x)
  change ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)
    (fieldInChosenClosure j D.complexEmbedding (D.fieldEmbedding x)) =
      algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q]) (HeckeCycles.QadicModelMap.CM.localFieldEmbedding J (D.fieldEmbedding x)) at h
  have hx : fieldInChosenClosure j D.complexEmbedding (D.fieldEmbedding x) = ιE x :=
    RingHom.congr_fun hE x
  rw [hx, ClosureSplitting.ParameterChoices.nativeClosureEmbedding_spec] at h
  exact h.symm

theorem nativeQadicChoice_closures :
    (nativeQadicChoice E D j ιE i f).complexClosure = j ∧
      (nativeQadicChoice E D j ιE i f).iota =
        ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false) ∧
      (nativeQadicChoice E D j ιE i f).fieldInClosure =
        (fieldInChosenClosure j D.complexEmbedding).toRingHom := ⟨rfl, rfl, rfl⟩

omit [Fact q.Prime] in
theorem exists_native_qadicChoice_bound (i : K →+* F) :
    ∃ d : ℕ, ∀ (q : ℕ) [Fact q.Prime], d < q → PELModuli.CMPoints.Arithmetic.SplitsCompletelyAt F q →
      ∀ (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (_hg : D.HasIntegralModelGeometry)
        (_hμ : D.reference.μ = E.val.toRingHom) (j : ParameterChoices.Qbar →+* ℂ) (ιE : E →ₐ[ℚ] ParameterChoices.Qbar),
        (∀ x : E, j (ιE x) = (x : ℂ)) →
      ∃ J : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q,
        J.complexClosure = j ∧
        J.iota = ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false) ∧
        J.fieldInClosure = (fieldInChosenClosure j D.complexEmbedding).toRingHom ∧
        (HeckeCycles.QadicModelMap.CM.localFieldEmbedding J).comp D.fieldEmbedding =
          LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false) := by
  obtain ⟨d, hd⟩ := PELModuli.CMPoints.LocalPadic.exists_padic_embedding_bound F
  refine ⟨d, fun q _ hq hs D hg hμ j ιE hι => ?_⟩
  obtain ⟨f⟩ := hd q hq hs
  exact ⟨nativeQadicChoice E D j ιE i f, rfl, rfl, rfl,
    nativeQadicChoice_local E D hg hμ j ιE hι i f⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CompatibleQadicChoice.ParameterChoices
