import OAI.NumberTheory.Adeles.LocalIntegers

/-! # Finite Norm -/

namespace OAI.NumberTheory.Adeles.FiniteNorm.CompletionFactors

noncomputable section

section

/-! The product of local relative norms over the places above a finite place. -/

open _root_.NumberField IsDedekindDomain HeightOneSpectrum
open scoped _root_.NumberField _root_.Topology OAI.NumberTheory.Adeles.LocalCompletions.CompletionFactors.FiniteLiesOver

variable {F E : Type*} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E]

abbrev FinitePlacesOver (E : Type*) [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) :=
  {w : HeightOneSpectrum (𝓞 E) // w.asIdeal.LiesOver v.asIdeal}

instance finitePlacesOver_liesOver (v : HeightOneSpectrum (𝓞 F))
    (w : FinitePlacesOver E v) : w.val.asIdeal.LiesOver v.asIdeal := w.property

instance finitePlacesOver_fintype (v : HeightOneSpectrum (𝓞 F)) :
    Fintype (FinitePlacesOver E v) :=
  Fintype.ofInjective
    (fun w : FinitePlacesOver E v =>
      (⟨w.val.asIdeal, w.val.isPrime, w.property⟩ : v.asIdeal.primesOver (𝓞 E))) (by
        intro a b h
        apply Subtype.ext
        apply HeightOneSpectrum.ext
        exact congrArg Subtype.val h)

omit [NumberField F] in
theorem finitePlace_under_eq (v : HeightOneSpectrum (𝓞 F))
    (w : FinitePlacesOver E v) : w.val.under (𝓞 F) = v := by
  apply HeightOneSpectrum.ext
  exact (Ideal.over_def w.val.asIdeal v.asIdeal).symm

/-- The `v` coordinate of the finite adelic norm. -/
def finiteNormCoordinate (v : HeightOneSpectrum (𝓞 F)) :
    LocalCompletions.CompletionFactors.FiniteAdele E →* v.adicCompletion F where
  toFun a := ∏ w : FinitePlacesOver E v, LocalNorms.CompletionFactors.finiteLocalNorm v w.val (a w.val)
  map_one' := by
    change (∏ w : FinitePlacesOver E v, LocalNorms.CompletionFactors.finiteLocalNorm v w.val 1) = 1
    simp
  map_mul' a b := by
    change (∏ w : FinitePlacesOver E v, LocalNorms.CompletionFactors.finiteLocalNorm v w.val (a w.val * b w.val)) = _
    simp only [map_mul, Finset.prod_mul_distrib]

theorem continuous_finiteNormCoordinate (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (finiteNormCoordinate (E := E) v) := by
  apply continuous_finsetProd
  intro w _
  have he : Continuous (fun a : LocalCompletions.CompletionFactors.FiniteAdele E => a w.val) :=
    RestrictedProduct.continuous_eval w.val
  exact (LocalNorms.CompletionFactors.continuous_finiteLocalNorm v w.val).comp he

theorem finiteNormCoordinate_integer (v : HeightOneSpectrum (𝓞 F)) (a : LocalCompletions.CompletionFactors.FiniteAdele E)
    (ha : ∀ w : FinitePlacesOver E v, a w.val ∈ w.val.adicCompletionIntegers E) :
    finiteNormCoordinate v a ∈ v.adicCompletionIntegers F := by
  apply Submonoid.prod_mem (Submonoid.ofClass (v.adicCompletionIntegers F))
  intro w _
  exact LocalIntegers.CompletionFactors.finiteLocalNorm_integer v w.val (a w.val) (ha w)

/-- Only finitely many target coordinates can fail to be integral. -/
theorem finiteNormCoordinate_eventually_integer (a : LocalCompletions.CompletionFactors.FiniteAdele E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      finiteNormCoordinate v a ∈ v.adicCompletionIntegers F := by
  have hbad : {w : HeightOneSpectrum (𝓞 E) | a w ∉ w.adicCompletionIntegers E}.Finite := a.2
  have hbase := hbad.image (HeightOneSpectrum.under (𝓞 F))
  filter_upwards [hbase.compl_mem_cofinite] with v hv
  apply finiteNormCoordinate_integer v a
  intro w
  by_contra hn
  exact hv ⟨w.val, hn, finitePlace_under_eq v w⟩

/-- The canonical relative norm on the finite adele rings, as a multiplicative map. -/
def finiteAdeleNorm : LocalCompletions.CompletionFactors.FiniteAdele E →* LocalCompletions.CompletionFactors.FiniteAdele F where
  toFun a := ⟨fun v => finiteNormCoordinate v a, finiteNormCoordinate_eventually_integer a⟩
  map_one' := by
    apply FiniteAdeleRing.ext
    intro v
    exact map_one (finiteNormCoordinate v)
  map_mul' a b := by
    apply FiniteAdeleRing.ext
    intro v
    exact map_mul (finiteNormCoordinate v) a b

@[simp] theorem finiteAdeleNorm_apply (a : LocalCompletions.CompletionFactors.FiniteAdele E) (v : HeightOneSpectrum (𝓞 F)) :
    finiteAdeleNorm a v = finiteNormCoordinate v a := rfl

end

/-! Continuity of the finite adelic norm for the restricted-product topology. -/

open _root_.NumberField IsDedekindDomain HeightOneSpectrum Filter
open scoped _root_.NumberField _root_.Topology RestrictedProduct

abbrev FiniteAdeleStage (K : Type*) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) :=
  Πʳ v : HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]_[principal S]

variable {F E : Type*} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E]

theorem continuous_finiteAdeleNorm : Continuous (finiteAdeleNorm (F := F) (E := E)) := by
  apply (RestrictedProduct.continuous_dom
    (R := fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E)
    (A := fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E)))
    (𝓕 := cofinite)).mpr
  intro S hS
  let T : Set (HeightOneSpectrum (𝓞 F)) :=
    (HeightOneSpectrum.under (𝓞 F) '' Sᶜ)ᶜ
  have hSc : Sᶜ.Finite := mem_cofinite.mp (le_principal_iff.mp hS)
  have hT : cofinite ≤ principal T :=
    le_principal_iff.mpr (hSc.image (HeightOneSpectrum.under (𝓞 F))).compl_mem_cofinite
  let inc : FiniteAdeleStage E S → LocalCompletions.CompletionFactors.FiniteAdele E :=
    RestrictedProduct.inclusion _ _ hS
  let fT : FiniteAdeleStage E S → FiniteAdeleStage F T := fun a =>
    ⟨fun v => finiteNormCoordinate v (inc a), by
      intro v hv
      apply finiteNormCoordinate_integer v (inc a)
      intro w
      have hw : w.val ∈ S := by
        by_contra hn
        exact hv ⟨w.val, hn, finitePlace_under_eq v w⟩
      exact a.2 hw⟩
  have hfT : Continuous fT := by
    apply RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr
    intro v
    exact (continuous_finiteNormCoordinate v).comp (RestrictedProduct.continuous_inclusion hS)
  have h := (RestrictedProduct.continuous_inclusion (R := fun v : HeightOneSpectrum (𝓞 F) =>
    v.adicCompletion F) (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) hT).comp hfT
  exact h

/-- The continuous relative norm on finite ideles. -/
def finiteIdeleNorm : (LocalCompletions.CompletionFactors.FiniteAdele E)ˣ →ₜ* (LocalCompletions.CompletionFactors.FiniteAdele F)ˣ where
  toMonoidHom := Units.map finiteAdeleNorm
  continuous_toFun := Continuous.units_map _ continuous_finiteAdeleNorm

end

end OAI.NumberTheory.Adeles.FiniteNorm.CompletionFactors
