import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization
import OAI.RepresentationTheory.Weil.AdelicSplitting.Rational

/-! # Assembly -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction

noncomputable section

section

/-! Actual compatible local data and the constructed adelic unitary lift.
The only splitting inputs are local. Adelic factorization is proved here;
rational compatibility is reserved for the AdelicSplitting target. -/

open Filter

variable (F : Type) [Field F] [NumberField F]
  (d : F) (n m : ℕ)
  (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)

abbrev localizedUnit {r : ℕ} (A : (Matrix (Fin r) (Fin r) (UnitaryBase.Construction.Quadratic F d))ˣ) (v : ArchimedeanAdeles.Construction.Places F) :
    (Matrix (Fin r) (Fin r) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ :=
  Units.map (Integral.Construction.rationalQuadraticLocal F d v).mapMatrix.toMonoidHom A

/-- A rational polarization and its local realizations. The compatibility
equation is an equality of linear coordinates on rational vectors; it says
nothing about Weil operators or splitting scalars. -/
structure GlobalFrames where
  rational : TensorSpace.Construction.SymplecticFrame d n m H.val K.val
  localFrame : ∀ v, TensorSpace.Construction.SymplecticFrame (ArchimedeanAdeles.Construction.rationalScalar F v d) n m
    (localizedUnit F d H v).val (localizedUnit F d K v).val
  coordinates_compatible : ∀ v (x : TensorSpace.Construction.TensorPosition d n m) i,
    (localFrame v).coordinates (fun j => Integral.Construction.rationalQuadraticLocal F d v (x j)) i =
      ArchimedeanAdeles.Construction.rationalScalar F v (rational.coordinates x i)

variable (hd : d ≠ 0) (C : Characters.Construction.GlobalCharacters F d n m) (P : GlobalFrames F d n m H K)

def localDualAction (v : ArchimedeanAdeles.Construction.Places F) :
    Integral.Construction.LocalUnitary F H.val v × Integral.Construction.LocalUnitary F K.val v →*
      Local.FunctionsMetaplectic.Construction.Symplectic (ArchimedeanAdeles.Construction.Completion F v) (n * m) :=
  TensorSpace.Construction.dualPairSymplectic (localizedUnit F d H v).val (localizedUnit F d K v).val
    (P.localFrame v)

/-- The actual local input to AdelicSplitting. The normalizing equations use the
prescribed global characters and the corrected weak open-cell integral. The
unramified condition refers to the explicitly constructed vacuum subgroup.
Neither adelic factorization nor rational compatibility is a field. -/
structure NormalizedLocalSplittings where
  atPlace : ∀ v, Integral.Construction.LocalUnitary F H.val v × Integral.Construction.LocalUnitary F K.val v →ₜ*
    Vacuum.Construction.CoverAt F (n * m) C.ψ v
  covers : ∀ v g, Vacuum.Construction.projectionAt F (n * m) C.ψ v (atPlace v g) =
    localDualAction F d n m H K P v g
  normalization : ∀ v, CorrectedNormalization.Construction.CorrectedLocalNormalization F d hd n m C v
    (localizedUnit F d H v) (localizedUnit F d K v) (P.localFrame v) (atPlace v)
  unramified : ∀ᶠ v in cofinite,
    Set.MapsTo (atPlace v) (Integral.Construction.localPairIntegral F H.val K.val v) (Vacuum.Construction.coverIntegral F (n * m) C.ψ v)

variable (D : NormalizedLocalSplittings F d n m H K hd C P)

def constructedAdelicLift : Integral.Construction.AdelicDualPair F H.val K.val →ₜ* Vacuum.Construction.GlobalCover F (n * m) C.ψ :=
  (CentralProduct.Construction.assembleCoverContinuous (Vacuum.Construction.coverIntegral F (n * m) C.ψ) (Vacuum.Construction.scalarAt F (n * m) C.ψ)).comp
    (RestrictedLimits.Construction.restrictedContinuousMap (Integral.Construction.localPairIntegral F H.val K.val)
      (Vacuum.Construction.coverIntegral F (n * m) C.ψ) D.atPlace D.unramified)

include D in
theorem localAction_integral : ∀ᶠ v in cofinite,
    Set.MapsTo
      (localDualAction F d n m H K P v)
      (Integral.Construction.localPairIntegral F H.val K.val v) (Vacuum.Construction.symplecticIntegral F (n * m) v) := by
  filter_upwards [D.unramified] with v hv
  intro g hg
  have h := Vacuum.Construction.coverIntegral_projects F (n * m) C.ψ v (hv hg)
  rwa [D.covers] at h

def adelicDualPairAction : Integral.Construction.AdelicDualPair F H.val K.val →* Vacuum.Construction.AdelicSymplectic F (n * m) :=
  RestrictedLimits.Construction.restrictedMap (Integral.Construction.localPairIntegral F H.val K.val) (Vacuum.Construction.symplecticIntegral F (n * m))
    (localDualAction F d n m H K P)
    (localAction_integral F d n m H K hd C P D)

theorem constructedAdelicLift_covers (g : Integral.Construction.AdelicDualPair F H.val K.val) :
    Vacuum.Construction.globalProjection F (n * m) C.ψ (constructedAdelicLift F d n m H K hd C P D g) =
      adelicDualPairAction F d n m H K hd C P D g := by
  apply RestrictedProduct.ext
  intro v
  exact D.covers v (g v)

theorem constructedAdelicLift_factors (v : ArchimedeanAdeles.Construction.Places F)
    (g : Integral.Construction.LocalUnitary F H.val v × Integral.Construction.LocalUnitary F K.val v) :
    constructedAdelicLift F d n m H K hd C P D (Integral.Construction.includeUnitaryPlace F H.val K.val v g) =
      Vacuum.Construction.globalInclude F (n * m) C.ψ v (D.atPlace v g) := by
  exact congrArg (CentralProduct.Construction.assembleCover (Vacuum.Construction.coverIntegral F (n * m) C.ψ) (Vacuum.Construction.scalarAt F (n * m) C.ψ))
    (RestrictedLimits.Construction.restrictedMap_includePlace (Integral.Construction.localPairIntegral F H.val K.val) (Vacuum.Construction.coverIntegral F (n * m) C.ψ)
      (fun v => (D.atPlace v).toMonoidHom) D.unramified v g)

end

/-! Rational base change for the explicit local normalizing scalars. -/

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)

theorem localDelta_eq_map (v : ArchimedeanAdeles.Construction.Places F) :
    Normalization.Construction.localDelta F d hd v =
      Units.map (Integral.Construction.rationalQuadraticLocal F d v).toMonoidHom (Normalization.Construction.deltaUnit d hd) := by
  apply Units.ext
  apply QuadraticAlgebra.ext <;> simp [Normalization.Construction.localDelta, Normalization.Construction.deltaUnit, Integral.Construction.rationalQuadraticLocal, UnitaryBase.Construction.quadraticBaseChange]

theorem determinant_localizedUnit {n : ℕ}
    (A : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ) (v : ArchimedeanAdeles.Construction.Places F) :
    Matrix.GeneralLinearGroup.det (localizedUnit F d A v) =
      Units.map (Integral.Construction.rationalQuadraticLocal F d v).toMonoidHom (Matrix.GeneralLinearGroup.det A) := by
  apply Units.ext
  exact (RingHom.map_det (Integral.Construction.rationalQuadraticLocal F d v) A.val).symm

theorem normCharacterScalar_one (v : ArchimedeanAdeles.Construction.Places F) : Normalization.Construction.normCharacterScalar F d v 1 = 1 := by
  rw [Normalization.Construction.normCharacterScalar, dite_eq_left one_ne_zero]
  have hu : Units.mk0 (1 : ArchimedeanAdeles.Construction.Completion F v) one_ne_zero = 1 := Units.ext rfl
  rw [hu]
  exact ite_eq_left ⟨1, map_one (Units.map QuadraticAlgebra.norm)⟩

theorem firstFactorScalar_zero_rank (n m : ℕ) (hN : n * m = 0)
    (C : Characters.Construction.GlobalCharacters F d n m) (v : ArchimedeanAdeles.Construction.Places F)
    (H : (Matrix (Fin n) (Fin n) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (K : (Matrix (Fin m) (Fin m) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (u : (Matrix (Fin n) (Fin n) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ) :
    Normalization.Construction.firstFactorScalar F d hd n m C v H K u =
      (Characters.Construction.localCharacter F d C.χW v
        ((Normalization.Construction.localDelta F d hd v) ^ n * Matrix.GeneralLinearGroup.det H * Matrix.GeneralLinearGroup.det u) : ℂ) := by
  rw [Normalization.Construction.firstFactorScalar, hN, pow_zero, one_mul]
  rcases Nat.mul_eq_zero.mp hN with hn | hm
  · simp [hn]
  · subst m
    have hK : K = 1 := Subsingleton.elim _ _
    simp [hK, QuadraticAlgebra.re_one, normCharacterScalar_one]

theorem secondFactorScalar_zero_rank (n m : ℕ) (hN : n * m = 0)
    (C : Characters.Construction.GlobalCharacters F d n m) (v : ArchimedeanAdeles.Construction.Places F)
    (H : (Matrix (Fin n) (Fin n) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (K : (Matrix (Fin m) (Fin m) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (u : (Matrix (Fin m) (Fin m) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ) :
    Normalization.Construction.secondFactorScalar F d n m C v H K u =
      (Characters.Construction.localCharacter F d C.χV v
        (Matrix.GeneralLinearGroup.det K * Matrix.GeneralLinearGroup.det u) : ℂ) := by
  rw [Normalization.Construction.secondFactorScalar, hN, pow_zero, one_mul]
  rcases Nat.mul_eq_zero.mp hN with hn | hm
  · subst n
    have hH : H = 1 := Subsingleton.elim _ _
    simp [hH, QuadraticAlgebra.re_one, normCharacterScalar_one]
  · simp [hm]

theorem correctedFirstFactorScalar_zero_rank (n m : ℕ) (hN : n * m = 0)
    (C : Characters.Construction.GlobalCharacters F d n m) (v : ArchimedeanAdeles.Construction.Places F)
    (H : (Matrix (Fin n) (Fin n) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (K : (Matrix (Fin m) (Fin m) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (u : (Matrix (Fin n) (Fin n) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ) :
    CorrectedNormalization.Construction.correctedFirstFactorScalar F d hd n m C v H K u =
      (Characters.Construction.localCharacter F d C.χW v
        ((Normalization.Construction.localDelta F d hd v) ^ n * Matrix.GeneralLinearGroup.det H * Matrix.GeneralLinearGroup.det u) : ℂ) := by
  rw [CorrectedNormalization.Construction.correctedFirstFactorScalar, hN, pow_zero, one_mul]
  rcases Nat.mul_eq_zero.mp hN with hn | hm
  · simp [hn]
  · subst m
    have hK : K = 1 := Subsingleton.elim _ _
    simp [hK, QuadraticAlgebra.re_one, normCharacterScalar_one]

theorem correctedSecondFactorScalar_zero_rank (n m : ℕ) (hN : n * m = 0)
    (C : Characters.Construction.GlobalCharacters F d n m) (v : ArchimedeanAdeles.Construction.Places F)
    (H : (Matrix (Fin n) (Fin n) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (K : (Matrix (Fin m) (Fin m) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (u : (Matrix (Fin m) (Fin m) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ) :
    CorrectedNormalization.Construction.correctedSecondFactorScalar F d n m C v H K u =
      (Characters.Construction.localCharacter F d C.χV v
        (Matrix.GeneralLinearGroup.det K * Matrix.GeneralLinearGroup.det u) : ℂ) := by
  rw [CorrectedNormalization.Construction.correctedSecondFactorScalar, hN, pow_zero, one_mul]
  rcases Nat.mul_eq_zero.mp hN with hn | hm
  · subst n
    have hH : H = 1 := Subsingleton.elim _ _
    simp [hH, QuadraticAlgebra.re_one, normCharacterScalar_one]
  · simp [hm]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction
