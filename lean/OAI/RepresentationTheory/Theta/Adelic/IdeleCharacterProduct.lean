import OAI.RepresentationTheory.Theta.Adelic.BaseLocalIdele
import OAI.RepresentationTheory.Weil.AdelicSplitting.Integral

/-! # Idele Character Product -/

namespace OAI.RepresentationTheory.Theta.Adelic.IdeleCharacterProduct

noncomputable section

/-! Assemble continuous local characters into a continuous character of
actual idele units when integral units are killed at almost every place. -/

open Filter Function
open scoped _root_.NumberField Classical _root_.Topology

open OAI.RepresentationTheory.Weil.AdelicSplitting.Integral.Construction

variable (F : Type) [Field F] [NumberField F]

def unitEvaluate (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)ˣ →ₜ* (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v)ˣ :=
  { Units.map (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.evaluate F v).toMonoidHom with
    continuous_toFun := (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.evaluate_continuous F v).units_map _ }

theorem unitEvaluate_val (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) (a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)ˣ) :
    (unitEvaluate F v a).val = Weil.AdelicSplitting.ArchimedeanAdeles.Construction.evaluate F v a.val := rfl

theorem unitEvaluate_inv (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) (a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)ˣ) :
    (unitEvaluate F v a).val⁻¹ = Weil.AdelicSplitting.ArchimedeanAdeles.Construction.evaluate F v a.inv := by
  have h : ((unitEvaluate F v a)⁻¹).val = Weil.AdelicSplitting.ArchimedeanAdeles.Construction.evaluate F v a.inv := rfl
  rwa [Units.val_inv_eq_inv_val] at h

variable (χ : ∀ v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F, (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v)ˣ →ₜ* Circle)
variable (hU : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) in cofinite,
  ∀ a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v))ˣ,
    a.val ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) → a.val⁻¹ ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) →
      χ (.inr v) a = 1)

include hU in
theorem localFactors_finite (a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)ˣ) :
    HasFiniteMulSupport (fun v => χ v (unitEvaluate F v a)) := by
  have htail : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) in cofinite,
      χ (.inr v) (unitEvaluate F (.inr v) a) = 1 := by
    filter_upwards [hU, a.val.2.property, a.inv.2.property] with v hv ha hi
    exact hv (unitEvaluate F (.inr v) a)
      (by rw [unitEvaluate_val]; exact ha) (by rw [unitEvaluate_inv]; exact hi)
  have hf : HasFiniteMulSupport (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      χ (.inr v) (unitEvaluate F (.inr v) a)) := htail
  apply ((Set.finite_range (Sum.inl : NumberField.InfinitePlace F → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F)).union
    (hf.image (Sum.inr : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F))).subset
  rintro (v | v) hv
  · exact Or.inl ⟨v, rfl⟩
  · exact Or.inr ⟨v, hv, rfl⟩

def productHom : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)ˣ →* Circle where
  toFun a := ∏ᶠ v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F, χ v (unitEvaluate F v a)
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul]
    exact finprod_mul_distrib (localFactors_finite F χ hU a) (localFactors_finite F χ hU b)

theorem productHom_continuous : Continuous (productHom F χ hU) := by
  apply continuous_of_continuousAt_one
  let s := (eventually_cofinite.mp hU).toFinset
  let t : Finset (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :=
    Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ s.map ⟨Sum.inr, Sum.inr_injective⟩
  have hgood (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (hv : v ∉ s) :
      ∀ a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v))ˣ,
        a.val ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) → a.val⁻¹ ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) →
          χ (.inr v) a = 1 := by
    simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hv
  have ho : IsOpen {a : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F |
      ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) => Valued.isOpen_valuationSubring (v.adicCompletion F))
  have hov := ho.preimage (continuous_snd.comp (Units.continuous_val (M := Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)))
  have hoi := ho.preimage (continuous_snd.comp (Units.continuous_coe_inv (M := Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)))
  have hevent : ∀ᶠ a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)ˣ in 𝓝 1,
      productHom F χ hU a = ∏ v ∈ t, χ v (unitEvaluate F v a) := by
    filter_upwards [(hov.inter hoi).mem_nhds (show (1 : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)ˣ) ∈ _ from
      ⟨fun v => (v.adicCompletionIntegers F).one_mem,
        fun v => (v.adicCompletionIntegers F).one_mem⟩)] with a ha
    apply finprod_eq_prod_of_mulSupport_subset
    rintro (v | v) hv
    · simp [t]
    · by_contra hvt
      have hvs : v ∉ s := by simpa [t] using hvt
      apply hv
      exact hgood v hvs (unitEvaluate F (.inr v) a)
        (by rw [unitEvaluate_val]; exact ha.1 v) (by rw [unitEvaluate_inv]; exact ha.2 v)
  have hp : Continuous (fun a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)ˣ => ∏ v ∈ t, χ v (unitEvaluate F v a)) :=
    continuous_finsetProd t (fun v _ => (χ v).continuous.comp (unitEvaluate F v).continuous)
  exact hp.continuousAt.congr_of_eventuallyEq hevent

def productCharacter : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)ˣ →ₜ* Circle :=
  ⟨productHom F χ hU, productHom_continuous F χ hU⟩

theorem productCharacter_local (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) (a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v)ˣ) :
    productCharacter F χ hU (BaseLocalIdele.baseLocalIdele F v a) = χ v a := by
  change (∏ᶠ w : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F, χ w
    (unitEvaluate F w (BaseLocalIdele.baseLocalIdele F v a))) = χ v a
  have he : unitEvaluate F v (BaseLocalIdele.baseLocalIdele F v a) = a := by
    apply Units.ext
    change Weil.AdelicSplitting.ArchimedeanAdeles.Construction.evaluate F v (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localAdd F v (a.val - 1) + 1) = a.val
    simp only [map_add, map_one, Weil.AdelicSplitting.ArchimedeanAdeles.Construction.evaluate_localAdd_same, sub_add_cancel]
  rw [finprod_eq_single _ v, he]
  intro w hw
  have hew : unitEvaluate F w (BaseLocalIdele.baseLocalIdele F v a) = 1 := by
    apply Units.ext
    change Weil.AdelicSplitting.ArchimedeanAdeles.Construction.evaluate F w (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localAdd F v (a.val - 1) + 1) = 1
    simp only [map_add, map_one, Weil.AdelicSplitting.ArchimedeanAdeles.Construction.evaluate_localAdd_other F hw, zero_add]
  rw [hew, map_one]

end

end OAI.RepresentationTheory.Theta.Adelic.IdeleCharacterProduct
