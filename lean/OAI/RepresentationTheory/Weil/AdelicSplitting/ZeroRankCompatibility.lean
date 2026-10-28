import OAI.RepresentationTheory.Weil.AdelicSplitting.NormalizationLevi
import OAI.RepresentationTheory.Weil.AdelicSplitting.Assembly
import OAI.RepresentationTheory.Weil.AdelicSplitting.CharacterProduct
import OAI.RepresentationTheory.Weil.AdelicSplitting.Scalars
import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalizationAnalysis

/-! # Zero Rank Compatibility -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ZeroRankCompatibility.Construction

noncomputable section

/-! Rational compatibility in tensor rank zero, with the corrected local
normalization and global principal-character conditions. -/

open _root_.MeasureTheory

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
  (n m : ℕ)
  (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (C : Characters.Construction.GlobalCharacters F d n m) (P : Assembly.Construction.GlobalFrames F d n m H K)
  (D : Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)

include D in
theorem constructedAdelicLift_rational_eq_one_of_local_scalars
    (g : UnitaryBase.Construction.Unitary H.val × UnitaryBase.Construction.Unitary K.val) (z : ArchimedeanAdeles.Construction.Places F → Circle)
    (hz : HasProd z 1)
    (ha : ∀ v, D.atPlace v (Integral.Construction.rationalPairLocal F H.val K.val v g) =
      Vacuum.Construction.scalarAt F (n * m) C.ψ v (z v)) :
    Assembly.Construction.constructedAdelicLift F d n m H K hd C P D (Integral.Construction.rationalPair F H.val K.val g) = 1 := by
  let w : ArchimedeanAdeles.Construction.Places F := .inl (Classical.choice inferInstance)
  exact Scalars.Construction.assemble_scalar_eq_one_of_hasProd F (n * m) C.ψ w
    (RestrictedLimits.Construction.restrictedMap (Integral.Construction.localPairIntegral F H.val K.val) (Vacuum.Construction.coverIntegral F (n * m) C.ψ)
      (fun v => (D.atPlace v).toMonoidHom) D.unramified (Integral.Construction.rationalPair F H.val K.val g)) z ha hz

include D in
theorem zeroRank_first_rational_open (hN : n * m = 0)
    (g : UnitaryBase.Construction.Unitary H.val) (hg : IsUnit (g.val.val - 1)) :
    Assembly.Construction.constructedAdelicLift F d n m H K hd C P D (Integral.Construction.rationalPair F H.val K.val (g, 1)) = 1 := by
  obtain ⟨u, hu⟩ := hg
  let a : (UnitaryBase.Construction.Quadratic F d)ˣ := (Normalization.Construction.deltaUnit d hd) ^ n * Matrix.GeneralLinearGroup.det H * Matrix.GeneralLinearGroup.det u
  let z : ArchimedeanAdeles.Construction.Places F → Circle := fun v => Characters.Construction.localCharacter F d C.χW v
    (Units.map (Integral.Construction.rationalQuadraticLocal F d v).toMonoidHom a)
  apply constructedAdelicLift_rational_eq_one_of_local_scalars F d hd n m H K C P D (g, 1) z
    (CharacterProduct.Construction.globalCharacters_chiW_hasProd F d n m C a)
  intro v
  let : Subsingleton (Local.FunctionsMetaplectic.Construction.Symplectic (ArchimedeanAdeles.Construction.Completion F v) (n * m)) := by
    rw [hN]
    infer_instance
  have hlocal : (Assembly.Construction.localizedUnit F d u v).val =
      (Integral.Construction.rationalUnitaryLocal F H.val v g).val.val - 1 := by
    change u.val.map (Integral.Construction.rationalQuadraticLocal F d v) =
      g.val.val.map (Integral.Construction.rationalQuadraticLocal F d v) - 1
    rw [hu]
    exact map_sub (Integral.Construction.rationalQuadraticLocal F d v).mapMatrix _ _ |>.trans
      (congrArg (g.val.val.map (Integral.Construction.rationalQuadraticLocal F d v) - ·)
        (map_one (Integral.Construction.rationalQuadraticLocal F d v).mapMatrix))
  have hs : CorrectedNormalization.Construction.correctedFirstFactorScalar F d hd n m C v (Assembly.Construction.localizedUnit F d H v)
      (Assembly.Construction.localizedUnit F d K v) (Assembly.Construction.localizedUnit F d u v) = (z v : ℂ) := by
    rw [Assembly.Construction.correctedFirstFactorScalar_zero_rank F d hd n m hN]
    simp only [Assembly.Construction.localDelta_eq_map, Assembly.Construction.determinant_localizedUnit, z, a, map_mul, map_pow]
  apply CorrectedNormalizationAnalysis.Construction.localCover_pairing_ext (Subsingleton.elim _ _)
  intro f h
  have he := (D.normalization v).1 (Integral.Construction.rationalUnitaryLocal F H.val v g)
    (Assembly.Construction.localizedUnit F d u v) hlocal f h
  have ho : ∀ (γ : Local.FunctionsMetaplectic.Construction.Symplectic (ArchimedeanAdeles.Construction.Completion F v) (n * m))
      (φ η : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F v) (n * m) → ℂ),
      CorrectedNormalization.Construction.correctedWeakOpenCellValue (ArchimedeanAdeles.Construction.Completion F v) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ v) γ φ η =
        ∫ x, φ x * star (η x) ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure (ArchimedeanAdeles.Construction.Completion F v) (n * m) := by
    rw [hN]
    exact CorrectedNormalizationAnalysis.Construction.correctedWeakOpenCellValue_zero_rank (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F C.ψ v)
  rw [ho, hs] at he
  change (∫ x, (Oscillator.Construction.localOperator _ _ _ (D.atPlace v (Integral.Construction.rationalUnitaryLocal F H.val v g, Integral.Construction.rationalUnitaryLocal F K.val v 1)) f).val x * star (h.val x)
      ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure (ArchimedeanAdeles.Construction.Completion F v) (n * m)) =
    ∫ x, ((z v : ℂ) * f.val x) * star (h.val x)
      ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure (ArchimedeanAdeles.Construction.Completion F v) (n * m)
  rw [map_one]
  simpa only [mul_assoc, integral_const_mul] using! he

include D in
theorem zeroRank_second_rational_open (hN : n * m = 0)
    (g : UnitaryBase.Construction.Unitary K.val) (hg : IsUnit (g.val.val - 1)) :
    Assembly.Construction.constructedAdelicLift F d n m H K hd C P D (Integral.Construction.rationalPair F H.val K.val (1, g)) = 1 := by
  obtain ⟨u, hu⟩ := hg
  let a : (UnitaryBase.Construction.Quadratic F d)ˣ := Matrix.GeneralLinearGroup.det K * Matrix.GeneralLinearGroup.det u
  let z : ArchimedeanAdeles.Construction.Places F → Circle := fun v => Characters.Construction.localCharacter F d C.χV v
    (Units.map (Integral.Construction.rationalQuadraticLocal F d v).toMonoidHom a)
  apply constructedAdelicLift_rational_eq_one_of_local_scalars F d hd n m H K C P D (1, g) z
    (CharacterProduct.Construction.globalCharacters_chiV_hasProd F d n m C a)
  intro v
  let : Subsingleton (Local.FunctionsMetaplectic.Construction.Symplectic (ArchimedeanAdeles.Construction.Completion F v) (n * m)) := by
    rw [hN]
    infer_instance
  have hlocal : (Assembly.Construction.localizedUnit F d u v).val =
      (Integral.Construction.rationalUnitaryLocal F K.val v g).val.val - 1 := by
    change u.val.map (Integral.Construction.rationalQuadraticLocal F d v) =
      g.val.val.map (Integral.Construction.rationalQuadraticLocal F d v) - 1
    rw [hu]
    exact map_sub (Integral.Construction.rationalQuadraticLocal F d v).mapMatrix _ _ |>.trans
      (congrArg (g.val.val.map (Integral.Construction.rationalQuadraticLocal F d v) - ·)
        (map_one (Integral.Construction.rationalQuadraticLocal F d v).mapMatrix))
  have hs : CorrectedNormalization.Construction.correctedSecondFactorScalar F d n m C v (Assembly.Construction.localizedUnit F d H v)
      (Assembly.Construction.localizedUnit F d K v) (Assembly.Construction.localizedUnit F d u v) = (z v : ℂ) := by
    rw [Assembly.Construction.correctedSecondFactorScalar_zero_rank F d n m hN]
    simp only [Assembly.Construction.determinant_localizedUnit, z, a, map_mul]
  apply CorrectedNormalizationAnalysis.Construction.localCover_pairing_ext (Subsingleton.elim _ _)
  intro f h
  have he := (D.normalization v).2 (Integral.Construction.rationalUnitaryLocal F K.val v g)
    (Assembly.Construction.localizedUnit F d u v) hlocal f h
  have ho : ∀ (γ : Local.FunctionsMetaplectic.Construction.Symplectic (ArchimedeanAdeles.Construction.Completion F v) (n * m))
      (φ η : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F v) (n * m) → ℂ),
      CorrectedNormalization.Construction.correctedWeakOpenCellValue (ArchimedeanAdeles.Construction.Completion F v) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ v) γ φ η =
        ∫ x, φ x * star (η x) ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure (ArchimedeanAdeles.Construction.Completion F v) (n * m) := by
    rw [hN]
    exact CorrectedNormalizationAnalysis.Construction.correctedWeakOpenCellValue_zero_rank (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F C.ψ v)
  rw [ho, hs] at he
  change (∫ x, (Oscillator.Construction.localOperator _ _ _ (D.atPlace v (Integral.Construction.rationalUnitaryLocal F H.val v 1, Integral.Construction.rationalUnitaryLocal F K.val v g)) f).val x * star (h.val x)
      ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure (ArchimedeanAdeles.Construction.Completion F v) (n * m)) =
    ∫ x, ((z v : ℂ) * f.val x) * star (h.val x)
      ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure (ArchimedeanAdeles.Construction.Completion F v) (n * m)
  rw [map_one]
  simpa only [mul_assoc, integral_const_mul] using! he

include D in
theorem constructedAdelicLift_rational_zero_rank (hns : ¬ IsSquare d) (hN : n * m = 0)
    (g : UnitaryBase.Construction.Unitary H.val × UnitaryBase.Construction.Unitary K.val) :
    Assembly.Construction.constructedAdelicLift F d n m H K hd C P D (Integral.Construction.rationalPair F H.val K.val g) = 1 := by
  let s : UnitaryBase.Construction.Unitary H.val × UnitaryBase.Construction.Unitary K.val →* Vacuum.Construction.GlobalCover F (n * m) C.ψ :=
    (Assembly.Construction.constructedAdelicLift F d n m H K hd C P D).toMonoidHom.comp
      (Integral.Construction.rationalPair F H.val K.val)
  have h₁ : s.comp (MonoidHom.inl _ _) = 1 :=
    NormalizationLevi.Construction.unitary_hom_ext_openCell d hns H.val _ _
      (zeroRank_first_rational_open F d hd n m H K C P D hN)
  have h₂ : s.comp (MonoidHom.inr _ _) = 1 :=
    NormalizationLevi.Construction.unitary_hom_ext_openCell d hns K.val _ _
      (zeroRank_second_rational_open F d hd n m H K C P D hN)
  change s g = 1
  have hg : g = (g.1, 1) * (1, g.2) := by simp
  rw [hg, map_mul]
  have he₁ : s (g.1, 1) = 1 := DFunLike.congr_fun h₁ g.1
  have he₂ : s (1, g.2) = 1 := DFunLike.congr_fun h₂ g.2
  rw [he₁, he₂, one_mul]

/-- The full AdelicSplitting conclusion when the tensor rank vanishes. -/
theorem adelic_unitary_splitting_zero_rank (hns : ¬ IsSquare d) (hN : n * m = 0) :
    (∀ g : Integral.Construction.AdelicDualPair F H.val K.val,
      Vacuum.Construction.globalProjection F (n * m) C.ψ
          (Assembly.Construction.constructedAdelicLift F d n m H K hd C P D g) =
        Assembly.Construction.adelicDualPairAction F d n m H K hd C P D g) ∧
    (∀ v (g : Integral.Construction.LocalUnitary F H.val v × Integral.Construction.LocalUnitary F K.val v),
      Assembly.Construction.constructedAdelicLift F d n m H K hd C P D
          (Integral.Construction.includeUnitaryPlace F H.val K.val v g) =
        Vacuum.Construction.globalInclude F (n * m) C.ψ v (D.atPlace v g)) ∧
    ∃ r : Local.FunctionsMetaplectic.Construction.Symplectic F (n * m) →* Vacuum.Construction.GlobalCover F (n * m) C.ψ,
      (∀ γ a, (γ, a) ∈ Rational.Construction.rationalGraph F (n * m) C.ψ ↔ r γ = a) ∧
      (∀ γ, Vacuum.Construction.globalProjection F (n * m) C.ψ (r γ) =
        Vacuum.Construction.rationalSymplectic F (n * m) γ) ∧
      (∀ g : UnitaryBase.Construction.Unitary H.val × UnitaryBase.Construction.Unitary K.val,
        Assembly.Construction.constructedAdelicLift F d n m H K hd C P D (Integral.Construction.rationalPair F H.val K.val g) =
          r (TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational g)) := by
  let : Subsingleton (Local.FunctionsMetaplectic.Construction.Symplectic F (n * m)) := by rw [hN]; infer_instance
  refine ⟨Assembly.Construction.constructedAdelicLift_covers F d n m H K hd C P D,
    Assembly.Construction.constructedAdelicLift_factors F d n m H K hd C P D, 1, ?_, ?_, ?_⟩
  · intro γ a
    have hgraph : Rational.Construction.rationalGraph F (n * m) C.ψ = ⊥ := by
      rw [hN]
      exact NormalizationLevi.Construction.rationalGraph_zero_rank F C.ψ
    rw [hgraph]
    change (γ, a) = (1, 1) ↔ 1 = a
    constructor
    · intro h
      exact (congrArg Prod.snd h).symm
    · intro h
      exact Prod.ext (Subsingleton.elim _ _) h.symm
  · intro γ
    have hγ : γ = 1 := Subsingleton.elim _ _
    change Vacuum.Construction.globalProjection F (n * m) C.ψ 1 = Vacuum.Construction.rationalSymplectic F (n * m) γ
    rw [hγ, map_one, map_one]
  · intro g
    exact constructedAdelicLift_rational_zero_rank F d hd n m H K C P D hns hN g

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ZeroRankCompatibility.Construction
