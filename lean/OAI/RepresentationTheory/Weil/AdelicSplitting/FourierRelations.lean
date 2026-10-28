import OAI.RepresentationTheory.Weil.AdelicSplitting.RationalFourier

/-! # Fourier Relations -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Weil.AdelicSplitting.FourierRelations.Construction

/-! Exact operator relations for the assembled rational Fourier generator. -/

theorem weylSymplectic_fourth (k : Type) [Field k] (N : ℕ) :
    Weil.Local.Generators.Construction.weylSymplectic k N ^ 4 = 1 := by
  apply Subtype.ext
  change (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) k) ^ 4 = 1
  have hW : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) k) =
      -Matrix.J (Fin N) k := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.J, Matrix.fromBlocks]
  rw [hW, show 4 = 2 * 2 from rfl, pow_mul]
  have h : (-Matrix.J (Fin N) k) ^ 2 = -1 := by simp [pow_two, Matrix.J_squared]
  rw [h]
  simp

section Local
variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
  (n m : ℕ) (hN : 0 < n * m)
  (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (C : Characters.Construction.GlobalCharacters F d n m) (P : Assembly.Construction.GlobalFrames F d n m H K)
  (D : Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)

include hN D in
theorem normalized_local_fourier_inversion (v : ArchimedeanAdeles.Construction.Places F)
    (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) (n * m)) (x : Weil.Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F v) (n * m)) :
    Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral (Characters.Construction.localAdditiveCharacter F C.ψ v)
      (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ v))
      (Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral (Characters.Construction.localAdditiveCharacter F C.ψ v)
        (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ v)) f.val) x = f.val (-x) := by
  cases v with
  | inr v => exact FiniteFourier.Construction.normalized_finite_fourier_inversion F d hd n m hN H K C P D v f x
  | inl v =>
      exact (ArchimedeanFourierCovers.Construction.archimedean_fourier_analysis F (n * m) v (Characters.Construction.localAdditiveCharacter F C.ψ (.inl v))
        (Characters.Construction.localAdditiveCharacter_continuous F C.ψ C.ψ_continuous (.inl v))
        (Characters.Construction.localAdditiveCharacter_unitary F C.ψ C.ψ_unitary (.inl v))
        (NontrivialLocalCharacter.Construction.normalizedLocalSplittings_character_nontrivial F d hd n m hN H K C P D (.inl v))).2 f x

theorem normalizedLocalFourierOscillator_square_apply (v : ArchimedeanAdeles.Construction.Places F)
    (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) (n * m)) (x : Weil.Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F v) (n * m)) :
    (((ArchimedeanFourierCovers.Construction.normalizedLocalFourierOscillator F d hd n m hN H K C P D v *
        ArchimedeanFourierCovers.Construction.normalizedLocalFourierOscillator F d hd n m hN H K C P D v).val.2) f).val x = f.val (-x) := by
  let T := ArchimedeanFourierCovers.Construction.normalizedLocalFourierOscillator F d hd n m hN H K C P D v
  have hT (g : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) (n * m)) : (T.val.2 g).val =
      Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral (Characters.Construction.localAdditiveCharacter F C.ψ v)
        (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ v)) g.val :=
    funext (ArchimedeanFourierCovers.Construction.normalizedLocalFourierOscillator_apply F d hd n m hN H K C P D v g)
  change (T.val.2 (T.val.2 f)).val x = _
  rw [hT, hT]
  exact normalized_local_fourier_inversion F d hd n m hN H K C P D v f x

theorem normalizedLocalFourierOscillator_fourth (v : ArchimedeanAdeles.Construction.Places F) :
    ArchimedeanFourierCovers.Construction.normalizedLocalFourierOscillator F d hd n m hN H K C P D v ^ 4 = 1 := by
  let T := ArchimedeanFourierCovers.Construction.normalizedLocalFourierOscillator F d hd n m hN H K C P D v
  apply NormalizationLevi.Construction.localCover_ext
  · rw [map_pow, map_one]
    change Vacuum.Construction.projectionAt F (n * m) C.ψ v T ^ 4 = 1
    rw [ArchimedeanFourierCovers.Construction.normalizedLocalFourierOscillator_covers]
    exact weylSymplectic_fourth _ _
  · intro f x
    have hp : T ^ 4 = (T * T) * (T * T) := by simp [pow_succ, mul_assoc]
    change ((T ^ 4).val.2 f).val x = f.val x
    rw [hp]
    change ((T * T).val.2 ((T * T).val.2 f)).val x = _
    rw [normalizedLocalFourierOscillator_square_apply,
      normalizedLocalFourierOscillator_square_apply, neg_neg]

end Local

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0) (hds : ¬ IsSquare d)
  (n m : ℕ) (hN : 0 < n * m)
  (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
  (C : Characters.Construction.GlobalCharacters F d n m) (P : Assembly.Construction.GlobalFrames F d n m H K)
  (D : Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)

theorem rationalFourierFamily_fourth :
    RationalFourier.Construction.rationalFourierFamily F d hd hds n m hN H K hH hK C P D ^ 4 = 1 := by
  apply RestrictedProduct.ext
  intro v
  exact normalizedLocalFourierOscillator_fourth F d hd n m hN H K C P D v

theorem rationalFourierLift_fourth :
    RationalFourier.Construction.rationalFourierLift F d hd hds n m hN H K hH hK C P D ^ 4 = 1 := by
  change Rational.Construction.assembleGlobalCover F (n * m) C.ψ (RationalFourier.Construction.rationalFourierFamily F d hd hds n m hN H K hH hK C P D) ^ 4 = 1
  rw [← map_pow, rationalFourierFamily_fourth, map_one]

end RepresentationTheory.Weil.AdelicSplitting.FourierRelations.Construction

namespace RepresentationTheory.Weil.AdelicSplitting.FourierRelations

/-! Fourier squared is the prescribed rational Levi lift of minus the
identity, locally and in the adelic cover. -/

namespace LocalAnalysis

theorem localModulus_of_square_one
    (k : Type) [NormedField k] [LocallyCompactSpace k] (a : kˣ) (ha : a * a = 1) :
    Weil.Local.FunctionsMetaplectic.Construction.localModulus k a = 1 := by
  have h : Weil.Local.FunctionsMetaplectic.Construction.localModulus k a * Weil.Local.FunctionsMetaplectic.Construction.localModulus k a = 1 := by
    rw [← Weil.Local.FunctionsMetaplectic.Construction.localModulus_mul, ha, Weil.Local.FunctionsMetaplectic.Construction.localModulus_one]
  have hp := Weil.Local.FunctionsMetaplectic.Construction.localModulus_pos k a
  nlinarith

theorem linearOscillator_neg_one_apply
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    (N : ℕ) (ψ : AddChar k ℂ) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (x : Weil.Local.FunctionsMetaplectic.Construction.Position k N) :
    ((NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator ψ (-1 : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N)).val.2 f).val x = f.val (-x) := by
  have hdet : Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k (-1 : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N) * Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k (-1 : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N) = 1 := by
    have h := congrArg (Units.map (Matrix.detMonoidHom : Matrix (Fin N) (Fin N) k →* k))
      (show (-1 : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N) * (-1) = 1 by simp)
    simpa only [map_mul, map_one] using! h
  rw [NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator_apply, localModulus_of_square_one k _ hdet]
  simp [Matrix.neg_mulVec]

end LocalAnalysis

namespace Construction
open OAI.RepresentationTheory.Weil.AdelicSplitting.FourierRelations.LocalAnalysis

theorem weylSymplectic_square (k : Type) [Field k] (N : ℕ) :
    Weil.Local.Generators.Construction.weylSymplectic k N * Weil.Local.Generators.Construction.weylSymplectic k N = Weil.Local.Generators.Construction.leviSymplectic (-1 : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N) := by
  apply Subtype.ext
  simp [Weil.Local.Generators.Construction.weylSymplectic, Weil.Local.Generators.Construction.leviSymplectic, Matrix.fromBlocks_multiply]

section Local
variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
  (n m : ℕ) (hN : 0 < n * m)
  (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (C : Characters.Construction.GlobalCharacters F d n m) (P : Assembly.Construction.GlobalFrames F d n m H K)
  (D : Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)

theorem normalizedLocalFourierOscillator_square (v : ArchimedeanAdeles.Construction.Places F) :
    ArchimedeanFourierCovers.Construction.normalizedLocalFourierOscillator F d hd n m hN H K C P D v *
      ArchimedeanFourierCovers.Construction.normalizedLocalFourierOscillator F d hd n m hN H K C P D v =
      NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator (Characters.Construction.localAdditiveCharacter F C.ψ v) (-1 : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear (ArchimedeanAdeles.Construction.Completion F v) (n * m)) := by
  apply NormalizationLevi.Construction.localCover_ext
  · rw [map_mul]
    change Vacuum.Construction.projectionAt F (n * m) C.ψ v (ArchimedeanFourierCovers.Construction.normalizedLocalFourierOscillator F d hd n m hN H K C P D v) *
      Vacuum.Construction.projectionAt F (n * m) C.ψ v (ArchimedeanFourierCovers.Construction.normalizedLocalFourierOscillator F d hd n m hN H K C P D v) =
      Weil.Local.Generators.Construction.leviSymplectic (-1 : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear (ArchimedeanAdeles.Construction.Completion F v) (n * m))
    rw [ArchimedeanFourierCovers.Construction.normalizedLocalFourierOscillator_covers, weylSymplectic_square]
  · intro f x
    change (((ArchimedeanFourierCovers.Construction.normalizedLocalFourierOscillator F d hd n m hN H K C P D v *
        ArchimedeanFourierCovers.Construction.normalizedLocalFourierOscillator F d hd n m hN H K C P D v).val.2) f).val x = _
    rw [normalizedLocalFourierOscillator_square_apply]
    exact (LocalAnalysis.linearOscillator_neg_one_apply (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ v) f x).symm

end Local

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0) (hds : ¬ IsSquare d)
  (n m : ℕ) (hN : 0 < n * m)
  (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
  (C : Characters.Construction.GlobalCharacters F d n m) (P : Assembly.Construction.GlobalFrames F d n m H K)
  (D : Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)

theorem rationalFourierFamily_square :
    RationalFourier.Construction.rationalFourierFamily F d hd hds n m hN H K hH hK C P D *
      RationalFourier.Construction.rationalFourierFamily F d hd hds n m hN H K hH hK C P D =
      RationalLevi.Construction.rationalLeviFamily F (n * m) C.ψ (-1 : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear F (n * m)) := by
  apply RestrictedProduct.ext
  intro v
  change ArchimedeanFourierCovers.Construction.normalizedLocalFourierOscillator F d hd n m hN H K C P D v *
      ArchimedeanFourierCovers.Construction.normalizedLocalFourierOscillator F d hd n m hN H K C P D v =
      NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator (Characters.Construction.localAdditiveCharacter F C.ψ v) (Rational.Construction.localizeLinear F (n * m) (-1) v)
  have hneg : Rational.Construction.localizeLinear F (n * m) (-1) v = (-1 : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear (ArchimedeanAdeles.Construction.Completion F v) (n * m)) := by
    apply Units.ext
    change ((-1 : Matrix (Fin (n * m)) (Fin (n * m)) F).map (ArchimedeanAdeles.Construction.rationalScalar F v)) = -1
    ext i j
    simp [Matrix.map_apply, Matrix.one_apply]
  rw [hneg]
  exact normalizedLocalFourierOscillator_square F d hd n m hN H K C P D v

theorem rationalFourierLift_square :
    RationalFourier.Construction.rationalFourierLift F d hd hds n m hN H K hH hK C P D *
      RationalFourier.Construction.rationalFourierLift F d hd hds n m hN H K hH hK C P D =
      NormalizationLevi.Construction.rationalLeviLift F (n * m) C.ψ (-1 : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear F (n * m)) := by
  have h := congrArg (Rational.Construction.assembleGlobalCover F (n * m) C.ψ)
    (rationalFourierFamily_square F d hd hds n m hN H K hH hK C P D)
  rw [map_mul] at h
  exact h

end Construction

end RepresentationTheory.Weil.AdelicSplitting.FourierRelations

end

end OAI
