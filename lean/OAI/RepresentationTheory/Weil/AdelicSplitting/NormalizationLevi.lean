import OAI.RepresentationTheory.Weil.AdelicSplitting.BaseChange
import OAI.RepresentationTheory.Weil.AdelicSplitting.UnitaryAlgebra
import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalizationAnalysis
import OAI.RepresentationTheory.Weil.AdelicSplitting.RationalLevi
import OAI.RepresentationTheory.Weil.AdelicSplitting.Normalization

/-! # Normalization Levi -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.NormalizationLevi.Construction

noncomputable section

section

/-! The prescribed local normalization determines the lift on rational
unitary points, including points outside the open cell. -/

open _root_.MeasureTheory

theorem localCover_ext
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] {N : ℕ} {ψ : AddChar k ℂ}
    {a b : Oscillator.Construction.LocalCover k N ψ}
    (hp : Oscillator.Construction.localProjection k N ψ a = Oscillator.Construction.localProjection k N ψ b)
    (ho : ∀ (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (x : Weil.Local.FunctionsMetaplectic.Construction.Position k N),
      (Oscillator.Construction.localOperator k N ψ a f).val x = (Oscillator.Construction.localOperator k N ψ b f).val x) : a = b := by
  apply Subtype.ext
  apply Prod.ext hp
  apply LinearEquiv.ext
  intro f
  apply Subtype.ext
  exact funext (ho f)

theorem unitary_hom_ext_openCell
    {F : Type*} [Field F] [CharZero F] (d : F) (hd : ¬ IsSquare d)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι (UnitaryBase.Construction.Quadratic F d)) {G : Type*} [Group G]
    (s t : UnitaryBase.Construction.Unitary H →* G)
    (h : ∀ (g : UnitaryBase.Construction.Unitary H), IsUnit (g.val.val - 1) → s g = t g) : s = t := by
  apply MonoidHom.ext
  intro g
  obtain ⟨a, b, rfl, ha, hb⟩ := UnitaryAlgebra.Construction.rational_unitary_open_factorization d hd H g
  rw [map_mul, map_mul, h a ha, h b hb]

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
  (n m : ℕ) (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (C : Characters.Construction.GlobalCharacters F d n m) (P : Assembly.Construction.GlobalFrames F d n m H K)
  (D E : Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)

theorem normalized_firstFactor_rational_open (v : ArchimedeanAdeles.Construction.Places F)
    (g : UnitaryBase.Construction.Unitary H.val) (hu : IsUnit (g.val.val - 1)) :
    D.atPlace v (Integral.Construction.rationalPairLocal F H.val K.val v (g, 1)) =
      E.atPlace v (Integral.Construction.rationalPairLocal F H.val K.val v (g, 1)) := by
  obtain ⟨u, hu⟩ := hu
  have hlocal : (Assembly.Construction.localizedUnit F d u v).val =
      (Integral.Construction.rationalUnitaryLocal F H.val v g).val.val - 1 := by
    change (u.val.map (Integral.Construction.rationalQuadraticLocal F d v)) =
      g.val.val.map (Integral.Construction.rationalQuadraticLocal F d v) - 1
    rw [hu]
    exact map_sub (Integral.Construction.rationalQuadraticLocal F d v).mapMatrix _ _ |>.trans
      (congrArg (g.val.val.map (Integral.Construction.rationalQuadraticLocal F d v) - ·)
        (map_one (Integral.Construction.rationalQuadraticLocal F d v).mapMatrix))
  apply CorrectedNormalizationAnalysis.Construction.localCover_pairing_ext
  · exact (D.covers v _).trans (E.covers v _).symm
  · intro f h
    have hD := (D.normalization v).1 (Integral.Construction.rationalUnitaryLocal F H.val v g)
      (Assembly.Construction.localizedUnit F d u v) hlocal f h
    have hE := (E.normalization v).1 (Integral.Construction.rationalUnitaryLocal F H.val v g)
      (Assembly.Construction.localizedUnit F d u v) hlocal f h
    change (∫ x, (Oscillator.Construction.localOperator _ _ _ (D.atPlace v
      (Integral.Construction.rationalUnitaryLocal F H.val v g, Integral.Construction.rationalUnitaryLocal F K.val v 1)) f).val x * star (h.val x)
        ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure (ArchimedeanAdeles.Construction.Completion F v) (n * m)) =
      ∫ x, (Oscillator.Construction.localOperator _ _ _ (E.atPlace v
      (Integral.Construction.rationalUnitaryLocal F H.val v g, Integral.Construction.rationalUnitaryLocal F K.val v 1)) f).val x * star (h.val x)
        ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure (ArchimedeanAdeles.Construction.Completion F v) (n * m)
    rw [map_one]
    exact hD.trans hE.symm

theorem normalized_secondFactor_rational_open (v : ArchimedeanAdeles.Construction.Places F)
    (g : UnitaryBase.Construction.Unitary K.val) (hu : IsUnit (g.val.val - 1)) :
    D.atPlace v (Integral.Construction.rationalPairLocal F H.val K.val v (1, g)) =
      E.atPlace v (Integral.Construction.rationalPairLocal F H.val K.val v (1, g)) := by
  obtain ⟨u, hu⟩ := hu
  have hlocal : (Assembly.Construction.localizedUnit F d u v).val =
      (Integral.Construction.rationalUnitaryLocal F K.val v g).val.val - 1 := by
    change (u.val.map (Integral.Construction.rationalQuadraticLocal F d v)) =
      g.val.val.map (Integral.Construction.rationalQuadraticLocal F d v) - 1
    rw [hu]
    exact map_sub (Integral.Construction.rationalQuadraticLocal F d v).mapMatrix _ _ |>.trans
      (congrArg (g.val.val.map (Integral.Construction.rationalQuadraticLocal F d v) - ·)
        (map_one (Integral.Construction.rationalQuadraticLocal F d v).mapMatrix))
  apply CorrectedNormalizationAnalysis.Construction.localCover_pairing_ext
  · exact (D.covers v _).trans (E.covers v _).symm
  · intro f h
    have hD := (D.normalization v).2 (Integral.Construction.rationalUnitaryLocal F K.val v g)
      (Assembly.Construction.localizedUnit F d u v) hlocal f h
    have hE := (E.normalization v).2 (Integral.Construction.rationalUnitaryLocal F K.val v g)
      (Assembly.Construction.localizedUnit F d u v) hlocal f h
    change (∫ x, (Oscillator.Construction.localOperator _ _ _ (D.atPlace v
      (Integral.Construction.rationalUnitaryLocal F H.val v 1, Integral.Construction.rationalUnitaryLocal F K.val v g)) f).val x * star (h.val x)
        ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure (ArchimedeanAdeles.Construction.Completion F v) (n * m)) =
      ∫ x, (Oscillator.Construction.localOperator _ _ _ (E.atPlace v
      (Integral.Construction.rationalUnitaryLocal F H.val v 1, Integral.Construction.rationalUnitaryLocal F K.val v g)) f).val x * star (h.val x)
        ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure (ArchimedeanAdeles.Construction.Completion F v) (n * m)
    rw [map_one]
    exact hD.trans hE.symm

theorem normalized_rational_unique (hns : ¬ IsSquare d) (v : ArchimedeanAdeles.Construction.Places F)
    (g : UnitaryBase.Construction.Unitary H.val × UnitaryBase.Construction.Unitary K.val) :
    D.atPlace v (Integral.Construction.rationalPairLocal F H.val K.val v g) =
      E.atPlace v (Integral.Construction.rationalPairLocal F H.val K.val v g) := by
  let s := (D.atPlace v).toMonoidHom.comp (Integral.Construction.rationalPairLocal F H.val K.val v)
  let t := (E.atPlace v).toMonoidHom.comp (Integral.Construction.rationalPairLocal F H.val K.val v)
  have h₁ : s.comp (MonoidHom.inl _ _) = t.comp (MonoidHom.inl _ _) :=
    unitary_hom_ext_openCell d hns H.val _ _
      (normalized_firstFactor_rational_open F d hd n m H K C P D E v)
  have h₂ : s.comp (MonoidHom.inr _ _) = t.comp (MonoidHom.inr _ _) :=
    unitary_hom_ext_openCell d hns K.val _ _
      (normalized_secondFactor_rational_open F d hd n m H K C P D E v)
  change s g = t g
  have hg : g = (g.1, 1) * (1, g.2) := by simp
  rw [hg, map_mul, map_mul]
  exact congrArg₂ (· * ·) (DFunLike.congr_fun h₁ g.1) (DFunLike.congr_fun h₂ g.2)

theorem constructedAdelicLift_rational_unique (hns : ¬ IsSquare d)
    (g : UnitaryBase.Construction.Unitary H.val × UnitaryBase.Construction.Unitary K.val) :
    Assembly.Construction.constructedAdelicLift F d n m H K hd C P D (Integral.Construction.rationalPair F H.val K.val g) =
      Assembly.Construction.constructedAdelicLift F d n m H K hd C P E (Integral.Construction.rationalPair F H.val K.val g) := by
  apply congrArg (CentralProduct.Construction.assembleCover (Vacuum.Construction.coverIntegral F (n * m) C.ψ) (Vacuum.Construction.scalarAt F (n * m) C.ψ))
  apply RestrictedProduct.ext
  intro v
  exact normalized_rational_unique F d hd n m H K C P D E hns v g

end

section

/-! The normalized rational Levi families form an actual homomorphism. -/

open scoped Classical

section Local
variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
  (N : ℕ) (ψ : AddChar k ℂ)

theorem linearOscillator_one : NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator ψ (1 : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N) = 1 := by
  apply localCover_ext
  · apply Subtype.ext
    simp [Oscillator.Construction.localProjection, NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator, Weil.Local.Generators.Construction.leviSymplectic]
  · intro f x
    change ((NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator ψ 1).val.2 f).val x = f.val x
    rw [NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator_apply]
    simp [Weil.Local.FunctionsMetaplectic.Construction.determinantUnit, Weil.Local.FunctionsMetaplectic.Construction.localModulus_one]

theorem linearOscillator_mul (A B : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N) :
    NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator ψ (A * B) = NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator ψ A * NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator ψ B := by
  apply localCover_ext
  · apply Subtype.ext
    change (Weil.Local.Generators.Construction.leviSymplectic (A * B)).val = (Weil.Local.Generators.Construction.leviSymplectic A).val * (Weil.Local.Generators.Construction.leviSymplectic B).val
    simp [Weil.Local.Generators.Construction.leviSymplectic, Matrix.fromBlocks_multiply, Matrix.transpose_mul]
  · intro f x
    change ((NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator ψ (A * B)).val.2 f).val x =
      ((NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator ψ A).val.2 ((NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator ψ B).val.2 f)).val x
    rw [NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator_apply, NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator_apply, NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator_apply]
    have hd : Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k (A * B) = Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k A * Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k B :=
      map_mul (Units.map (Matrix.detMonoidHom : Matrix (Fin N) (Fin N) k →* k)) A B
    rw [hd, Weil.Local.FunctionsMetaplectic.Construction.localModulus_mul, Real.sqrt_mul (Weil.Local.FunctionsMetaplectic.Construction.localModulus_pos k _).le]
    simp only [mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec,
      Complex.ofReal_mul, mul_assoc]
    rw [mul_left_comm]

def localLeviHom : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N →* Oscillator.Construction.LocalCover k N ψ where
  toFun := NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator ψ
  map_one' := linearOscillator_one N ψ
  map_mul' := linearOscillator_mul N ψ

end Local

variable (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)

def rationalLeviRestrictedHom : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear F N →* Rational.Construction.RestrictedCover F N ψ where
  toFun := RationalLevi.Construction.rationalLeviFamily F N ψ
  map_one' := by
    apply RestrictedProduct.ext
    intro v
    change NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator (Characters.Construction.localAdditiveCharacter F ψ v)
      (Units.map (ArchimedeanAdeles.Construction.rationalScalar F v).mapMatrix.toMonoidHom 1) = 1
    rw [map_one]
    exact linearOscillator_one N _
  map_mul' A B := by
    apply RestrictedProduct.ext
    intro v
    change NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator (Characters.Construction.localAdditiveCharacter F ψ v)
      (Units.map (ArchimedeanAdeles.Construction.rationalScalar F v).mapMatrix.toMonoidHom (A * B)) =
        NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator (Characters.Construction.localAdditiveCharacter F ψ v) (Rational.Construction.localizeLinear F N A v) *
        NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator (Characters.Construction.localAdditiveCharacter F ψ v) (Rational.Construction.localizeLinear F N B v)
    rw [map_mul]
    exact linearOscillator_mul N _ _ _

def rationalLeviLift : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear F N →* Vacuum.Construction.GlobalCover F N ψ :=
  (Rational.Construction.assembleGlobalCover F N ψ).comp (rationalLeviRestrictedHom F N ψ)

theorem rationalLeviLift_mem_graph (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear F N) :
    (Weil.Local.Generators.Construction.leviSymplectic A, rationalLeviLift F N ψ A) ∈ Rational.Construction.rationalGraph F N ψ :=
  RationalLevi.Construction.rationalGraph_contains_levi F N ψ A

theorem rationalLeviLift_covers (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear F N) :
    Vacuum.Construction.globalProjection F N ψ (rationalLeviLift F N ψ A) =
      Vacuum.Construction.rationalSymplectic F N (Weil.Local.Generators.Construction.leviSymplectic A) :=
  Rational.Construction.assembled_covers_rational F N ψ _ _ (RationalLevi.Construction.rationalLeviFamily_spec F N ψ A).1

theorem isRationalLevi_unique (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear F N)
    {a b : Rational.Construction.RestrictedCover F N ψ} (ha : Rational.Construction.IsRationalLevi F N ψ A a)
    (hb : Rational.Construction.IsRationalLevi F N ψ A b) : a = b := by
  apply RestrictedProduct.ext
  intro v
  apply localCover_ext ((ha.1 v).trans (hb.1 v).symm)
  intro f x
  exact (ha.2 v f x).trans (hb.2 v f x).symm

theorem isRationalQuadratic_unique (B : Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix F N)
    {a b : Rational.Construction.RestrictedCover F N ψ} (ha : Rational.Construction.IsRationalQuadratic F N ψ B a)
    (hb : Rational.Construction.IsRationalQuadratic F N ψ B b) : a = b := by
  apply RestrictedProduct.ext
  intro v
  apply localCover_ext ((ha.1 v).trans (hb.1 v).symm)
  intro f x
  exact (ha.2 v f x).trans (hb.2 v f x).symm

theorem isRationalFourier_unique
    {a b : Rational.Construction.RestrictedCover F N ψ} (ha : Rational.Construction.IsRationalFourier F N ψ a)
    (hb : Rational.Construction.IsRationalFourier F N ψ b) : a = b := by
  apply RestrictedProduct.ext
  intro v
  apply localCover_ext ((ha.1 v).trans (hb.1 v).symm)
  intro f x
  exact (ha.2 v f x).trans (hb.2 v f x).symm

end

/-! The prescribed rational graph in rank zero, including the raw Fourier
formula. This handles the degenerate rank directly from the definitions. -/

open _root_.MeasureTheory

theorem fourierIntegral_zero_rank
    (k : Type) [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k ℂ)
    (f : Weil.Local.FunctionsMetaplectic.Construction.Position k 0 → ℂ) (x : Weil.Local.FunctionsMetaplectic.Construction.Position k 0) :
    Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure k 0 ψ) f x = f x := by
  rw [Weil.Local.FunctionsMetaplectic.Construction.positionMeasure, Measure.pi_of_empty _ x]
  simp [Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral, Weil.Local.FunctionsMetaplectic.Construction.dot]

theorem openCellOperator_zero_rank
    (k : Type) [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k ℂ)
    (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k 0) (f : Weil.Local.FunctionsMetaplectic.Construction.Position k 0 → ℂ) (x : Weil.Local.FunctionsMetaplectic.Construction.Position k 0) :
    Normalization.Construction.openCellOperator k 0 ψ g f x = f x := by
  have hg : g = 1 := Subsingleton.elim _ _
  subst g
  have hs : Normalization.Construction.openCellScale k 0 1 = 1 := by
    simp [Normalization.Construction.openCellScale, Matrix.det_isEmpty, Weil.Local.FunctionsMetaplectic.Construction.localModulus_one]
  have he (ε : ℝ) : Normalization.Construction.dampedIntertwiner k 0 ψ 1 ε f x = f x := by
    rw [Normalization.Construction.dampedIntertwiner, hs, Measure.pi_of_empty _ (0 : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k 0)]
    simp [Normalization.Construction.phasePair, Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction, Matrix.toBilin'_apply ]
  simp only [Normalization.Construction.openCellOperator, he]
  exact tendsto_const_nhds.limUnder_eq

variable (F : Type) [Field F] [NumberField F] (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)

theorem isRationalLevi_zero_rank (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear F 0)
    {a : Rational.Construction.RestrictedCover F 0 ψ} (ha : Rational.Construction.IsRationalLevi F 0 ψ A a) : a = 1 := by
  apply RestrictedProduct.ext
  intro v
  apply localCover_ext (Subsingleton.elim _ _)
  intro f x
  have hA : Rational.Construction.localizeLinear F 0 A v = 1 := Subsingleton.elim _ _
  have h := ha.2 v f x
  rw [hA] at h
  simpa [Weil.Local.FunctionsMetaplectic.Construction.determinantUnit, Weil.Local.FunctionsMetaplectic.Construction.localModulus_one, Weil.Local.FunctionsMetaplectic.Construction.substitutionOperator_apply] using h

theorem isRationalQuadratic_zero_rank (B : Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix F 0)
    {a : Rational.Construction.RestrictedCover F 0 ψ} (ha : Rational.Construction.IsRationalQuadratic F 0 ψ B a) : a = 1 := by
  apply RestrictedProduct.ext
  intro v
  apply localCover_ext (Subsingleton.elim _ _)
  intro f x
  simpa using ha.2 v f x

theorem isRationalFourier_zero_rank
    {a : Rational.Construction.RestrictedCover F 0 ψ} (ha : Rational.Construction.IsRationalFourier F 0 ψ a) : a = 1 := by
  apply RestrictedProduct.ext
  intro v
  apply localCover_ext (Subsingleton.elim _ _)
  intro f x
  exact (ha.2 v f x).trans (fourierIntegral_zero_rank _ _ _ _)

theorem isRationalFourier_zero_rank_one : Rational.Construction.IsRationalFourier F 0 ψ 1 := by
  constructor
  · intro v
    exact Subsingleton.elim _ _
  · intro v f x
    exact (fourierIntegral_zero_rank _ _ _ _).symm

theorem rationalGraph_zero_rank : Rational.Construction.rationalGraph F 0 ψ = ⊥ := by
  apply le_antisymm _ bot_le
  apply (Subgroup.closure_le ⊥).mpr
  intro z hz
  rcases hz with ⟨A, a, ha, rfl⟩ | ⟨B, a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · rw [isRationalLevi_zero_rank F ψ A ha]
    exact Prod.ext (Subsingleton.elim _ _) (map_one (Rational.Construction.assembleGlobalCover F 0 ψ))
  · rw [isRationalQuadratic_zero_rank F ψ B ha]
    exact Prod.ext (Subsingleton.elim _ _) (map_one (Rational.Construction.assembleGlobalCover F 0 ψ))
  · rw [isRationalFourier_zero_rank F ψ ha]
    exact Prod.ext (Subsingleton.elim _ _) (map_one (Rational.Construction.assembleGlobalCover F 0 ψ))

theorem rationalGraph_zero_rank_realization :
    ∃ r : Weil.Local.FunctionsMetaplectic.Construction.Symplectic F 0 →* Vacuum.Construction.GlobalCover F 0 ψ,
      (∀ γ a, (γ, a) ∈ Rational.Construction.rationalGraph F 0 ψ ↔ r γ = a) ∧
      ∀ γ, Vacuum.Construction.globalProjection F 0 ψ (r γ) = Vacuum.Construction.rationalSymplectic F 0 γ := by
  refine ⟨1, ?_, ?_⟩
  · intro γ a
    rw [rationalGraph_zero_rank]
    change (γ, a) = (1, 1) ↔ 1 = a
    constructor
    · intro h
      exact (congrArg Prod.snd h).symm
    · intro h
      exact Prod.ext (Subsingleton.elim _ _) h.symm
  · intro γ
    have hγ : γ = 1 := Subsingleton.elim _ _
    simp [hγ]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.NormalizationLevi.Construction
