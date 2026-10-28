import OAI.RepresentationTheory.Theta.Kernel.IntrinsicArchimedeanIndependence

/-! # Intrinsic Multiplicity Operator -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Kernel.IntrinsicMultiplicityOperator.Intrinsic

/-! The actual multiplicity-space oscillator operators commute with
the actual SU(V) operators. Hence moving an archimedean test in the W
factor preserves theta invariance at the original finite stabilizer. -/

open scoped _root_.NumberField Classical

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta

variable (F : Type) [Field F] [NumberField F]

local instance (v : NumberField.InfinitePlace F) : MeasurableSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := borel _
local instance (v : NumberField.InfinitePlace F) : BorelSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := ⟨rfl⟩

variable {d : F} {m : ℕ}
variable (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (hd : d ≠ 0) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)
variable (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
variable (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C P)

abbrev ArchMultiplicity := ∀ v : NumberField.InfinitePlace F, Weil.AdelicSplitting.Integral.Construction.LocalUnitary F K.val (.inl v)

def multiplicityOperator (w : ArchMultiplicity F K) :
    Adelic.ThetaEvaluation.ArchimedeanTests F (3 * m) ≃ₗ[ℂ] Adelic.ThetaEvaluation.ArchimedeanTests F (3 * m) :=
  LinearEquiv.piCongrRight (fun v =>
    Weil.AdelicSplitting.Oscillator.Construction.localOperator (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) (3 * m) (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inl v))
      (D.atPlace (.inl v) (1,w v)))

theorem multiplicity_operator_commutes (w : ArchMultiplicity F K)
    (g : Adelic.RationalSU.ArchimedeanSU F H) (φ : Adelic.ThetaEvaluation.ArchimedeanTests F (3 * m)) :
    multiplicityOperator F H K hd P C D w (Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D g φ) =
      Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D g (multiplicityOperator F H K hd P C D w φ) := by
  funext v
  let ρ := (Weil.AdelicSplitting.Oscillator.Construction.localOperator (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) (3 * m)
    (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inl v))).comp (D.atPlace (.inl v)).toMonoidHom
  change ρ (1,w v) (ρ (Adelic.SpecialUnitary.includeUnitary _ (g v),1) (φ v)) =
    ρ (Adelic.SpecialUnitary.includeUnitary _ (g v),1) (ρ (1,w v) (φ v))
  rw [← LinearEquiv.mul_apply,← LinearEquiv.mul_apply,← map_mul,← map_mul]
  simp only [Prod.mul_def,one_mul,mul_one]

theorem moved_test_theta_covariance
    (hns : ¬ IsSquare d) (hH : H.val.conjTranspose = H.val)
    (hK : K.val.conjTranspose = -K.val)
    (w : ArchMultiplicity F K) (g : Adelic.SpecialUnitary.SU H.val)
    (φ : Adelic.ThetaEvaluation.ArchimedeanTests F (3 * m)) (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * m)) :
    Adelic.ThetaEvaluation.theta F (3 * m)
      (multiplicityOperator F H K hd P C D w
        (Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D (Adelic.RationalSU.rationalArchimedeanSU F H g) φ))
      (Adelic.FiniteSchwartz.finiteAction F H K hd C P D (Adelic.RationalSU.rationalFiniteSU F H g) f) =
        Adelic.ThetaEvaluation.theta F (3 * m) (multiplicityOperator F H K hd P C D w φ) f := by
  rw [multiplicity_operator_commutes]
  exact Adelic.SpecialUnitaryTheta.rational_specialUnitary_theta F H K hd C P D hns hH hK g _ f

theorem moved_test_theta_fixed_level
    (hns : ¬ IsSquare d) (hH : H.val.conjTranspose = H.val)
    (hK : K.val.conjTranspose = -K.val)
    (w : ArchMultiplicity F K) (g : Adelic.SpecialUnitary.SU H.val)
    (φ : Adelic.ThetaEvaluation.ArchimedeanTests F (3 * m)) (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (hf : Adelic.FiniteSchwartz.finiteAction F H K hd C P D (Adelic.RationalSU.rationalFiniteSU F H g) f = f) :
    Adelic.ThetaEvaluation.theta F (3 * m)
      (multiplicityOperator F H K hd P C D w
        (Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D (Adelic.RationalSU.rationalArchimedeanSU F H g) φ)) f =
      Adelic.ThetaEvaluation.theta F (3 * m) (multiplicityOperator F H K hd P C D w φ) f := by
  simpa only [hf] using moved_test_theta_covariance F H K hd P C D hns hH hK w g φ f

end RepresentationTheory.Theta.Kernel.IntrinsicMultiplicityOperator.Intrinsic

namespace RepresentationTheory.Theta.Kernel.IntrinsicMultiplicityOperator.IntrinsicCommutingArch

/-! Any actual local oscillator family commuting with the native SU
action preserves theta covariance at the original finite stabilizer. -/

open scoped _root_.NumberField Classical

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta

variable (F : Type) [Field F] [NumberField F]

local instance (v : NumberField.InfinitePlace F) : MeasurableSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := borel _
local instance (v : NumberField.InfinitePlace F) : BorelSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := ⟨rfl⟩

variable {d : F} {m : ℕ}
variable (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (hd : d ≠ 0) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
variable (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C P)

def archOperator (b : ∀ v : NumberField.InfinitePlace F, Weil.AdelicSplitting.Vacuum.Construction.CoverAt F (3 * m) C.ψ (.inl v)) :
    Adelic.ThetaEvaluation.ArchimedeanTests F (3 * m) ≃ₗ[ℂ] Adelic.ThetaEvaluation.ArchimedeanTests F (3 * m) :=
  LinearEquiv.piCongrRight (fun v => Weil.AdelicSplitting.Oscillator.Construction.localOperator _ _ _ (b v))

theorem arch_operator_commutes
    (b : ∀ v : NumberField.InfinitePlace F, Weil.AdelicSplitting.Vacuum.Construction.CoverAt F (3 * m) C.ψ (.inl v))
    (hb : ∀ v g, Commute (b v) (Adelic.FiniteSchwartz.localSUSplitting F H K hd C P D (.inl v) g))
    (g : Adelic.RationalSU.ArchimedeanSU F H) (φ : Adelic.ThetaEvaluation.ArchimedeanTests F (3 * m)) :
    archOperator F C b (Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D g φ) =
      Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D g (archOperator F C b φ) := by
  funext v
  change Weil.AdelicSplitting.Oscillator.Construction.localOperator _ _ _ (b v)
    (Weil.AdelicSplitting.Oscillator.Construction.localOperator _ _ _ (Adelic.FiniteSchwartz.localSUSplitting F H K hd C P D (.inl v) (g v)) (φ v)) =
      Weil.AdelicSplitting.Oscillator.Construction.localOperator _ _ _ (Adelic.FiniteSchwartz.localSUSplitting F H K hd C P D (.inl v) (g v))
        (Weil.AdelicSplitting.Oscillator.Construction.localOperator _ _ _ (b v) (φ v))
  rw [← LinearEquiv.mul_apply,← map_mul,(hb v (g v)).eq,map_mul,LinearEquiv.mul_apply]

theorem arch_operator_theta_fixed_level
    (hns : ¬ IsSquare d) (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (b : ∀ v : NumberField.InfinitePlace F, Weil.AdelicSplitting.Vacuum.Construction.CoverAt F (3 * m) C.ψ (.inl v))
    (hb : ∀ v g, Commute (b v) (Adelic.FiniteSchwartz.localSUSplitting F H K hd C P D (.inl v) g))
    (g : Adelic.SpecialUnitary.SU H.val) (φ : Adelic.ThetaEvaluation.ArchimedeanTests F (3 * m)) (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (hf : Adelic.FiniteSchwartz.finiteAction F H K hd C P D (Adelic.RationalSU.rationalFiniteSU F H g) f = f) :
    Adelic.ThetaEvaluation.theta F (3 * m)
      (archOperator F C b (Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D (Adelic.RationalSU.rationalArchimedeanSU F H g) φ)) f =
        Adelic.ThetaEvaluation.theta F (3 * m) (archOperator F C b φ) f := by
  rw [arch_operator_commutes F H K hd P C D b hb]
  have he := Adelic.SpecialUnitaryTheta.rational_specialUnitary_theta F H K hd C P D hns hH hK g (archOperator F C b φ) f
  rw [hf] at he
  exact he

end RepresentationTheory.Theta.Kernel.IntrinsicMultiplicityOperator.IntrinsicCommutingArch

namespace RepresentationTheory.Theta.Kernel.IntrinsicMultiplicityOperator.IntrinsicConjugated

/-! Conjugating the actual compact multiplicity operators by a native
SU-centralizing oscillator family preserves the original finite-level
theta covariance. -/

open scoped _root_.NumberField Classical

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation OAI.RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicMultiplicityOperator.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicMultiplicityOperator.IntrinsicCommutingArch

theorem pair_factor_commutes {G J E : Type*} [Group G] [Group J] [Group E]
    (s : G × J →* E) (g : G) (w : J) : Commute (s (1,w)) (s (g,1)) := by
  change s (1,w) * s (g,1) = s (g,1) * s (1,w)
  rw [← map_mul,← map_mul]
  simp only [Prod.mul_def,one_mul,mul_one]

theorem conjugate_commutes {E : Type*} [Group E] (b w s : E)
    (hb : Commute b s) (hw : Commute w s) : Commute (b⁻¹ * w * b) s :=
  ((Commute.inv_left_iff.mpr hb).mul_left hw).mul_left hb

variable (F : Type) [Field F] [NumberField F]

local instance (v : NumberField.InfinitePlace F) : MeasurableSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := borel _
local instance (v : NumberField.InfinitePlace F) : BorelSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := ⟨rfl⟩

variable {d : F} {m : ℕ}
variable (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
variable (hd : d ≠ 0) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
variable (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C P)

def conjugatedMultiplicityFamily
    (b : ∀ v : NumberField.InfinitePlace F, Weil.AdelicSplitting.Vacuum.Construction.CoverAt F (3 * m) C.ψ (.inl v))
    (w : Intrinsic.ArchMultiplicity F K) (v : NumberField.InfinitePlace F) : Weil.AdelicSplitting.Vacuum.Construction.CoverAt F (3 * m) C.ψ (.inl v) :=
  (b v)⁻¹ * D.atPlace (.inl v) (1,w v) * b v

theorem conjugated_multiplicity_commutes
    (b : ∀ v : NumberField.InfinitePlace F, Weil.AdelicSplitting.Vacuum.Construction.CoverAt F (3 * m) C.ψ (.inl v))
    (hb : ∀ v g, Commute (b v) (Adelic.FiniteSchwartz.localSUSplitting F H K hd C P D (.inl v) g))
    (w : Intrinsic.ArchMultiplicity F K) (v : NumberField.InfinitePlace F)
    (g : Adelic.SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl v))) :
    Commute (conjugatedMultiplicityFamily F H K hd P C D b w v)
      (Adelic.FiniteSchwartz.localSUSplitting F H K hd C P D (.inl v) g) := by
  exact conjugate_commutes (b v) (D.atPlace (.inl v) (1,w v))
    (Adelic.FiniteSchwartz.localSUSplitting F H K hd C P D (.inl v) g) (hb v g)
      (pair_factor_commutes (D.atPlace (.inl v)).toMonoidHom (Adelic.SpecialUnitary.includeUnitary _ g) (w v))

theorem conjugated_multiplicity_theta_fixed_level
    (hns : ¬ IsSquare d) (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (b : ∀ v : NumberField.InfinitePlace F, Weil.AdelicSplitting.Vacuum.Construction.CoverAt F (3 * m) C.ψ (.inl v))
    (hb : ∀ v g, Commute (b v) (Adelic.FiniteSchwartz.localSUSplitting F H K hd C P D (.inl v) g))
    (w : Intrinsic.ArchMultiplicity F K) (g : Adelic.SpecialUnitary.SU H.val) (φ : Adelic.ThetaEvaluation.ArchimedeanTests F (3 * m))
    (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (hf : Adelic.FiniteSchwartz.finiteAction F H K hd C P D (Adelic.RationalSU.rationalFiniteSU F H g) f = f) :
    Adelic.ThetaEvaluation.theta F (3 * m)
      (IntrinsicCommutingArch.archOperator F C (conjugatedMultiplicityFamily F H K hd P C D b w)
        (Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D (Adelic.RationalSU.rationalArchimedeanSU F H g) φ)) f =
      Adelic.ThetaEvaluation.theta F (3 * m) (IntrinsicCommutingArch.archOperator F C (conjugatedMultiplicityFamily F H K hd P C D b w) φ) f :=
  IntrinsicCommutingArch.arch_operator_theta_fixed_level F H K hd P C D hns hH hK _
    (conjugated_multiplicity_commutes F H K hd P C D b hb w) g φ f hf

end RepresentationTheory.Theta.Kernel.IntrinsicMultiplicityOperator.IntrinsicConjugated

end

end OAI
