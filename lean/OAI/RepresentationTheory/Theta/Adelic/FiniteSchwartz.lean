import OAI.RepresentationTheory.Theta.Adelic.IntegralTopology
import OAI.RepresentationTheory.Theta.Adelic.TensorProjective
import OAI.RepresentationTheory.Weil.AdelicSplitting.NontrivialLocalCharacter
import OAI.RepresentationTheory.Weil.AdelicSplitting.RationalLevi

/-! # Finite Schwartz -/

namespace OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

noncomputable section

/-! The actual finite Schwartz restricted tensor product and the action
obtained by restricting AdelicSplitting's local splittings to determinant-one matrices.
All smoothness claims are derived from local compactly supported functions. -/

open scoped _root_.NumberField _root_.Topology
open Filter

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.IntegralTopology

variable (F : Type) [Field F] [NumberField F]

abbrev FinitePlace := IsDedekindDomain.HeightOneSpectrum (𝓞 F)

local instance (v : FinitePlace F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (v : FinitePlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
local instance (v : FinitePlace F) : CharZero (v.adicCompletion F) := Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionCharZero F (.inr v)

abbrev finiteSchwartz (N : ℕ) :=
  TensorProjective.Restricted.restrictedTensor (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N)

variable {n m : ℕ} {d : F}
    (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)

abbrev FiniteSU := Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup (fun v : FinitePlace F => IntegralTopology.localSUIntegral F H.val (.inr v))

variable (hd : d ≠ 0) (C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d n m) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d n m H K)
    (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)

def localSUToPair (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :
    SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val v) →ₜ* Weil.AdelicSplitting.Integral.Construction.LocalUnitary F H.val v × Weil.AdelicSplitting.Integral.Construction.LocalUnitary F K.val v where
  toFun g := (SpecialUnitary.includeUnitary _ g, 1)
  map_one' := by simp
  map_mul' g h := by simp
  continuous_toFun := (SpecialUnitary.includeUnitaryContinuous _).continuous.prodMk continuous_const

def localSUSplitting (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :
    SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val v) →ₜ* Weil.AdelicSplitting.Vacuum.Construction.CoverAt F (n * m) C.ψ v :=
  (D.atPlace v).comp (localSUToPair F H K v)

def localSUAction (v : FinitePlace F) :
    SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v)) →*
      (Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m) ≃ₗ[ℂ]
        Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m)) :=
  (Weil.AdelicSplitting.Oscillator.Construction.localOperator (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m) (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))).comp
    (localSUSplitting F H K hd C P D (.inr v)).toMonoidHom

theorem localSUAction_unramified :
    ∀ᶠ v : FinitePlace F in cofinite, ∀ g ∈ IntegralTopology.localSUIntegral F H.val (.inr v),
      localSUAction F H K hd C P D v g (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m) v) = Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m) v := by
  have h := (Sum.inr_injective.tendsto_cofinite).eventually D.unramified
  filter_upwards [h] with v hv
  intro g hg
  exact (hv (show localSUToPair F H K (.inr v) g ∈ Weil.AdelicSplitting.Integral.Construction.localPairIntegral F H.val K.val (.inr v) from
    ⟨hg, (Weil.AdelicSplitting.Integral.Construction.localUnitaryIntegral F K.val (.inr v)).one_mem⟩)).2

def finiteAction : FiniteSU F H →*
    (finiteSchwartz F (n * m) ≃ₗ[ℂ] finiteSchwartz F (n * m)) :=
  TensorProjective.Restricted.action (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m))
    (fun v : FinitePlace F => IntegralTopology.localSUIntegral F H.val (.inr v))
    (localSUAction F H K hd C P D) (localSUAction_unramified F H K hd C P D)

theorem localSUAction_smooth (hN : 0 < n * m) (v : FinitePlace F)
    (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m)) :
    IsOpen {g | localSUAction F H K hd C P D v g f = f} := by
  let : MeasurableSpace (v.adicCompletion F) := borel _
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let : CharZero (v.adicCompletion F) := Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionCharZero F (.inr v)
  let : NontriviallyNormedField (v.adicCompletion F) :=
    Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))
  have hk : ¬ DiscreteTopology (v.adicCompletion F) := by
    intro h
    let : DiscreteTopology (v.adicCompletion F) := h
    exact not_isOpen_singleton (0 : v.adicCompletion F) (isOpen_discrete _)
  exact RestrictedSmoothness.restricted_action_smooth
    (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
    (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_continuous F C.ψ C.ψ_continuous (.inr v))
    (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_unitary F C.ψ C.ψ_unitary (.inr v)) hk
    (Weil.AdelicSplitting.NontrivialLocalCharacter.Construction.normalizedLocalSplittings_character_nontrivial F d hd n m hN H K C P D (.inr v))
    (localSUSplitting F H K hd C P D (.inr v)) f

theorem finiteAction_smooth (hN : 0 < n * m) (f : finiteSchwartz F (n * m)) :
    IsOpen {g : FiniteSU F H | finiteAction F H K hd C P D g f = f} :=
  TensorProjective.Restricted.action_smooth (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F (n * m))
    (fun v : FinitePlace F => IntegralTopology.localSUIntegral F H.val (.inr v))
    (localSUAction F H K hd C P D) (localSUAction_unramified F H K hd C P D)
    (fun v => IntegralTopology.localSUIntegral_open F H.val (.inr v))
    (localSUAction_smooth F H K hd C P D hN) f

end

end OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
