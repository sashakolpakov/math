import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalizationAnalysis
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacters
import OAI.RepresentationTheory.Weil.AdelicSplitting.FieldTransport
import OAI.RepresentationTheory.Weil.AdelicSplitting.Assembly

/-! # Nontrivial Local Character -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.NontrivialLocalCharacter.Construction

noncomputable section

/-! Local nontriviality follows from the prescribed local normalization in
positive tensor dimension: an invertible oscillator operator cannot vanish. -/

open scoped ContDiff

theorem archimedean_test_one
    (k : Type) [NormedField k] [NormedAlgebra ℝ k] [FiniteDimensional ℝ k] (N : ℕ) :
    ∃ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N, f.val 0 = 1 := by
  let b : ContDiffBump (0 : Local.FunctionsMetaplectic.Construction.Position k N) := default
  have hs : HasCompactSupport (fun x => (b x : ℂ)) :=
    b.hasCompactSupport.comp_left (show ((0 : ℝ) : ℂ) = 0 from rfl)
  have hc : ContDiff ℝ ∞ (fun x => (b x : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
  let φ := hs.toSchwartzMap hc
  refine ⟨⟨φ, ArchimedeanCharacters.LocalAnalysis.schwartzBruhat_archimedean_iff.mpr ⟨φ, rfl⟩⟩, ?_⟩
  change (b 0 : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
  rfl

theorem local_test_one (F : Type) [Field F] [NumberField F] (N : ℕ) (v : ArchimedeanAdeles.Construction.Places F) :
    ∃ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) N, f.val 0 = 1 := by
  cases v with
  | inr v => exact ⟨Vacuum.Construction.finiteVacuum F N v, Vacuum.Construction.finiteVacuum_zero F N v⟩
  | inl v =>
      rcases v.isReal_or_isComplex with hv | hv
      · let e := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv
        let p := FieldTransport.LocalAnalysis.positionFieldEquiv N e
          (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).continuous
          (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous
        obtain ⟨f, hf⟩ := archimedean_test_one ℝ N
        refine ⟨⟨f.val ∘ p, FieldTransport.LocalAnalysis.schwartzBruhat_comp_fieldAddEquiv p f.property⟩, ?_⟩
        change f.val (p 0) = 1
        rwa [map_zero]
      · let e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
        let p := FieldTransport.LocalAnalysis.positionFieldEquiv N e
          (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).continuous
          (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm.continuous
        obtain ⟨f, hf⟩ := archimedean_test_one ℂ N
        refine ⟨⟨f.val ∘ p, FieldTransport.LocalAnalysis.schwartzBruhat_comp_fieldAddEquiv p f.property⟩, ?_⟩
        change f.val (p 0) = 1
        rwa [map_zero]

def negativeUnitary {R : Type*} [CommRing R] [StarRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι R) : UnitaryBase.Construction.Unitary H :=
  ⟨-1, by
    change (-1 : Matrix ι ι R).conjTranspose * H * (-1) = H
    simp⟩

theorem negativeUnitary_open
    {k : Type*} [Field k] [CharZero k] (d : k)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι (UnitaryBase.Construction.Quadratic k d)) :
    IsUnit ((negativeUnitary H).val.val - 1) := by
  have h := (isUnit_iff_ne_zero.mpr (by norm_num : (-2 : k) ≠ 0)).map
    (algebraMap k (Matrix ι ι (UnitaryBase.Construction.Quadratic k d)))
  convert h using 1
  change (-1 : Matrix ι ι (UnitaryBase.Construction.Quadratic k d)) - 1 = _
  simp only [map_neg, map_ofNat]
  norm_num [sub_eq_add_neg, one_add_one_eq_two]

theorem normalizedLocalSplittings_character_nontrivial
    (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
    (n m : ℕ) (hN : 0 < n * m)
    (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
    (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
    (C : Characters.Construction.GlobalCharacters F d n m) (P : Assembly.Construction.GlobalFrames F d n m H K)
    (D : Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P) (v : ArchimedeanAdeles.Construction.Places F) :
    ∃ t : ArchimedeanAdeles.Construction.Completion F v, Characters.Construction.localAdditiveCharacter F C.ψ v t ≠ 1 := by
  by_contra! htrivial
  let g : Integral.Construction.LocalUnitary F H.val v := negativeUnitary (Assembly.Construction.localizedUnit F d H v).val
  obtain ⟨u, hu⟩ := negativeUnitary_open (ArchimedeanAdeles.Construction.rationalScalar F v d) (Assembly.Construction.localizedUnit F d H v).val
  obtain ⟨f, hf⟩ := local_test_one F (n * m) v
  have hzero : Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ v)
      (D.atPlace v (g, 1)) f = 0 := by
    apply CorrectedNormalizationAnalysis.Construction.integral_test_pairing_ext
    intro h
    have hD := (D.normalization v).1 g u hu f h
    rw [CorrectedNormalizationAnalysis.Construction.correctedWeakOpenCellValue_trivial (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F C.ψ v)
      htrivial (n * m) hN, mul_zero] at hD
    simpa only [Submodule.coe_zero, Pi.zero_apply, zero_mul, MeasureTheory.integral_zero] using! hD
  have hfzero : f = 0 :=
    (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ v)
      (D.atPlace v (g, 1))).injective (hzero.trans (map_zero _).symm)
  rw [hfzero] at hf
  exact zero_ne_one hf

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.NontrivialLocalCharacter.Construction
