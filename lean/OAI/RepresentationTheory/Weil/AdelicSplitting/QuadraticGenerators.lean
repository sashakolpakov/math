import OAI.RepresentationTheory.Weil.AdelicSplitting.RationalLevi
import OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanIntertwiner
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacters
import OAI.RepresentationTheory.Weil.AdelicSplitting.FieldTransport
import OAI.RepresentationTheory.Weil.AdelicSplitting.UnramifiedCharacter

/-! # Quadratic Generators -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.QuadraticGenerators.Construction

noncomputable section

/-! Actual quadratic oscillator generators at all places of a number field. -/

open Filter
open scoped Classical _root_.NumberField

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
  (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hu : ∀ x, ‖ψ x‖ = 1) (hc : Continuous ψ)

include hu hc in
theorem localQuadratic_stability (v : ArchimedeanAdeles.Construction.Places F)
    (B : Matrix (Fin N) (Fin N) (ArchimedeanAdeles.Construction.Completion F v)) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N) :
    Local.FunctionsMetaplectic.Construction.quadraticOperator (Characters.Construction.localAdditiveCharacter F ψ v) B f.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N := by
  cases v with
  | inl v =>
      rcases v.isReal_or_isComplex with hv | hv
      · let e := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv
        have he : Continuous e :=
          (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).continuous
        have hi : Continuous e.symm :=
          (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous
        apply FieldTransport.LocalAnalysis.quadratic_stability_fieldTransport e he hi _ _ B f
        intro A g
        apply ArchimedeanCharacters.LocalAnalysis.quadraticOperator_archimedean_mem _ _ A g.property
        exact ArchimedeanCharacters.LocalAnalysis.real_character_temperate _
          ((Characters.Construction.localAdditiveCharacter_continuous F ψ hc (.inl v)).comp hi)
          (fun t => Characters.Construction.localAdditiveCharacter_unitary F ψ hu (.inl v) _)
      · let e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
        have he : Continuous e :=
          (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).continuous
        have hi : Continuous e.symm :=
          (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm.continuous
        apply FieldTransport.LocalAnalysis.quadratic_stability_fieldTransport e he hi _ _ B f
        intro A g
        apply ArchimedeanCharacters.LocalAnalysis.quadraticOperator_archimedean_mem _ _ A g.property
        exact ArchimedeanCharacters.LocalAnalysis.complex_character_temperate _
          ((Characters.Construction.localAdditiveCharacter_continuous F ψ hc (.inl v)).comp hi)
          (fun t => Characters.Construction.localAdditiveCharacter_unitary F ψ hu (.inl v) _)
  | inr v =>
      exact NonarchimedeanIntertwiner.LocalAnalysis.nonarchimedean_quadratic_mem (Characters.Construction.localAdditiveCharacter F ψ (.inr v))
        (Characters.Construction.localAdditiveCharacter_unitary F ψ hu (.inr v))
        (Characters.Construction.localAdditiveCharacter_continuous F ψ hc (.inr v)) B f

def quadraticAtPlace (v : ArchimedeanAdeles.Construction.Places F) (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix (ArchimedeanAdeles.Construction.Completion F v) N) : Vacuum.Construction.CoverAt F N ψ v :=
  NonarchimedeanIntertwiner.LocalAnalysis.quadraticOscillator (Characters.Construction.localAdditiveCharacter F ψ v) (localQuadratic_stability F N ψ hu hc v)
    (Characters.Construction.localAdditiveCharacter_unitary F ψ hu v) B

theorem quadraticAtPlace_covers (v : ArchimedeanAdeles.Construction.Places F) (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix (ArchimedeanAdeles.Construction.Completion F v) N) :
    Vacuum.Construction.projectionAt F N ψ v (quadraticAtPlace F N ψ hu hc v B) = Local.Generators.Construction.quadraticSymplectic B := rfl

theorem quadraticAtPlace_apply (v : ArchimedeanAdeles.Construction.Places F) (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix (ArchimedeanAdeles.Construction.Completion F v) N)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N) (x : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F v) N) :
    (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)
      (quadraticAtPlace F N ψ hu hc v B) f).val x =
        Characters.Construction.localAdditiveCharacter F ψ v (Local.FunctionsMetaplectic.Construction.quadratic B.val x) * f.val x := rfl

theorem finite_quadratic_vacuum
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix (ArchimedeanAdeles.Construction.Completion F (.inr v)) N)
    (hB : ∀ i j, B.val i j / 2 ∈ v.adicCompletionIntegers F)
    (hψ : ∀ x ∈ v.adicCompletionIntegers F, Characters.Construction.localAdditiveCharacter F ψ (.inr v) x = 1) :
    (quadraticAtPlace F N ψ hu hc (.inr v) B).val.2 (Vacuum.Construction.finiteVacuum F N v) =
      Vacuum.Construction.finiteVacuum F N v := by
  apply Subtype.ext
  funext x
  rw [show ((quadraticAtPlace F N ψ hu hc (.inr v) B).val.2 (Vacuum.Construction.finiteVacuum F N v)).val x =
    Characters.Construction.localAdditiveCharacter F ψ (.inr v) (Local.FunctionsMetaplectic.Construction.quadratic B.val x) * (Vacuum.Construction.finiteVacuum F N v).val x from
      quadraticAtPlace_apply F N ψ hu hc (.inr v) B (Vacuum.Construction.finiteVacuum F N v) x]
  by_cases hx : x ∈ Vacuum.Construction.finitePositionLattice F N v
  · have hq : Local.FunctionsMetaplectic.Construction.quadratic B.val x ∈ v.adicCompletionIntegers F := by
      have he : Local.FunctionsMetaplectic.Construction.quadratic B.val x = ∑ i, ∑ j, x i * (B.val i j / 2) * x j := by
        simp only [Local.FunctionsMetaplectic.Construction.quadratic, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [he]
      apply (v.adicCompletionIntegers F).sum_mem
      intro i _
      apply (v.adicCompletionIntegers F).sum_mem
      intro j _
      exact (v.adicCompletionIntegers F).toSubring.mul_mem
        ((v.adicCompletionIntegers F).toSubring.mul_mem (hx i (Set.mem_univ i)) (hB i j))
        (hx j (Set.mem_univ j))
    rw [hψ _ hq, one_mul]
  · have hzero : (Vacuum.Construction.finiteVacuum F N v).val x = 0 := Set.indicator_of_notMem hx _
    rw [hzero, mul_zero]

def localizeQuadratic (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F N) (v : ArchimedeanAdeles.Construction.Places F) :
    Local.FunctionsMetaplectic.Construction.SymmetricMatrix (ArchimedeanAdeles.Construction.Completion F v) N :=
  ⟨B.val.map (ArchimedeanAdeles.Construction.rationalScalar F v), B.property.map _⟩

def rationalQuadraticFamilyLocal (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F N) (v : ArchimedeanAdeles.Construction.Places F) : Vacuum.Construction.CoverAt F N ψ v :=
  quadraticAtPlace F N ψ hu hc v (localizeQuadratic F N B v)

theorem rationalQuadraticFamilyLocal_covers (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F N) (v : ArchimedeanAdeles.Construction.Places F) :
    Vacuum.Construction.projectionAt F N ψ v (rationalQuadraticFamilyLocal F N ψ hu hc B v) =
      Vacuum.Construction.rationalSymplecticLocal F N v (Local.Generators.Construction.quadraticSymplectic B) := by
  apply Subtype.ext
  ext i j
  cases i <;> cases j <;>
    simp [rationalQuadraticFamilyLocal, quadraticAtPlace, NonarchimedeanIntertwiner.LocalAnalysis.quadraticOscillator,
      Vacuum.Construction.projectionAt, Oscillator.Construction.localProjection, Local.Generators.Construction.quadraticSymplectic, localizeQuadratic,
      Vacuum.Construction.rationalSymplecticLocal, Vacuum.Construction.mapSymplectic, Matrix.fromBlocks, Matrix.one_apply]

theorem rationalQuadraticFamilyLocal_integral (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F N) :
    ∀ᶠ v in cofinite, rationalQuadraticFamilyLocal F N ψ hu hc B v ∈ Vacuum.Construction.coverIntegral F N ψ v := by
  have hhalf : ∀ᶠ v in cofinite, ∀ i j,
      ArchimedeanAdeles.Construction.rationalScalar F v (B.val i j / 2) ∈ Integral.Construction.localIntegerRing F v :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun j =>
      Integral.Construction.rationalScalar_integral F (B.val i j / 2)))
  have hchar := UnramifiedCharacter.Construction.eventually_cofinite_sum_right (I := NumberField.InfinitePlace F) _
    (UnramifiedCharacter.Construction.localAdditiveCharacter_unramified_finite F ψ hu hc)
  filter_upwards [Vacuum.Construction.rationalSymplecticLocal_integral F N (Local.Generators.Construction.quadraticSymplectic B), hhalf, hchar]
    with v hp hB hψ
  refine ⟨?_, ?_⟩
  · change Vacuum.Construction.projectionAt F N ψ v (rationalQuadraticFamilyLocal F N ψ hu hc B v) ∈
      Vacuum.Construction.symplecticIntegral F N v
    rwa [rationalQuadraticFamilyLocal_covers]
  · cases v with
    | inl v => trivial
    | inr v =>
        apply finite_quadratic_vacuum F N ψ hu hc v (localizeQuadratic F N B (.inr v)) _ hψ
        intro i j
        change ArchimedeanAdeles.Construction.rationalScalar F (.inr v) (B.val i j) / 2 ∈ Integral.Construction.localIntegerRing F (.inr v)
        simpa only [map_div₀, map_ofNat] using hB i j

def rationalQuadraticFamily (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F N) : Rational.Construction.RestrictedCover F N ψ :=
  ⟨rationalQuadraticFamilyLocal F N ψ hu hc B,
    rationalQuadraticFamilyLocal_integral F N ψ hu hc B⟩

theorem rationalQuadraticFamily_spec (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F N) :
    Rational.Construction.IsRationalQuadratic F N ψ B (rationalQuadraticFamily F N ψ hu hc B) := by
  constructor
  · exact rationalQuadraticFamilyLocal_covers F N ψ hu hc B
  · intro v f x
    rfl

theorem rationalGraph_contains_quadratic (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F N) :
    (Local.Generators.Construction.quadraticSymplectic B, Rational.Construction.assembleGlobalCover F N ψ (rationalQuadraticFamily F N ψ hu hc B)) ∈
      Rational.Construction.rationalGraph F N ψ :=
  Subgroup.subset_closure (Or.inr (Or.inl ⟨B, rationalQuadraticFamily F N ψ hu hc B,
    rationalQuadraticFamily_spec F N ψ hu hc B, rfl⟩))

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.QuadraticGenerators.Construction
