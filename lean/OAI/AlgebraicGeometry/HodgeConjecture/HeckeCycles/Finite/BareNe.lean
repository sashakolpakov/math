import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.Schur

/-! # Bare Ne -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareNe.CM.OscillatorKernel

/-! The actual finite oscillator projection has scalar unitary kernel.
This identifies its kernel inside the operator group, without asserting
the stronger two-fold exactness needed for the bare metaplectic cover. -/

open scoped Classical
open _root_.MeasureTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator.CM

variable {I : Type*} [Fintype I]

theorem integralPairing_smul (c : ℂ) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    FiniteOscillator.CM.integralPairing (c • f) (c • f) = (c * star c) * FiniteOscillator.CM.integralPairing f f := by
  change (∫ x, (c * f.val x) * star (c * f.val x) ∂(Constructed.FiniteMeasure.CM.measure I)) = _
  simp_rw [star_mul]
  calc
    _ = ∫ x, (c * star c) * (f.val x * star (f.val x)) ∂(Constructed.FiniteMeasure.CM.measure I) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by ring)
    _ = _ := integral_const_mul _ _

theorem integralTest_pairing :
    FiniteOscillator.CM.integralPairing (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction (ι := I)) RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction = 1 := by
  have hpoint (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator x * star (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator x) = RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator x := by
    by_cases hx : x ∈ RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors
    · rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator_of_mem hx, star_one, mul_one]
    · rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator_of_notMem hx, zero_mul]
  change (∫ x, RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator x * star (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator x) ∂(Constructed.FiniteMeasure.CM.measure I)) = 1
  simp_rw [hpoint]
  unfold RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator
  rw [integral_indicator RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors_isClopen.isClosed.measurableSet]
  simpa using congrArg (fun t : ℝ => (t : ℂ)) (Constructed.FiniteMeasure.CM.integral_real_volume I)

theorem kernel_scalar (g : FiniteOscillator.CM.Oscillator (I := I)) (hg : FiniteOscillator.CM.projection g = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I, FiniteOscillator.CM.action g f = c • f := by
  have hT : LatticeEigenline.CM.CommutesFiniteHeisenberg (FiniteOscillator.CM.action g).toLinearMap := by
    intro p q f h hh x
    have he := g.property.2 (Sum.elim p q) f h
    have hgp : g.val.1 = 1 := hg
    rw [hgp, FiniteOscillator.CM.phaseAction_one] at he
    exact congrFun (he.mp (funext hh)) x
  let c := (FiniteOscillator.CM.action g RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction).val 0
  have hc (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : FiniteOscillator.CM.action g f = c • f :=
    Schur.CM.finite_heisenberg_commutant_scalar (FiniteOscillator.CM.action g).toLinearMap hT f
  have h := FiniteOscillator.CM.unitary g RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction
  rw [hc, integralPairing_smul, integralTest_pairing, mul_one] at h
  have hn : ‖c‖ * ‖c‖ = 1 := by
    simpa only [norm_mul, norm_star, norm_one] using congrArg norm h
  exact ⟨c, by nlinarith [norm_nonneg c], hc⟩

theorem faithful : Function.Injective (fun g : FiniteOscillator.CM.Oscillator (I := I) => (FiniteOscillator.CM.projection g, FiniteOscillator.CM.action g)) := by
  intro g h he
  exact Subtype.ext he

theorem kernel_central (g : FiniteOscillator.CM.Oscillator (I := I)) (hg : FiniteOscillator.CM.projection g = 1)
    (h : FiniteOscillator.CM.Oscillator (I := I)) : Commute g h := by
  obtain ⟨c, _, hc⟩ := kernel_scalar g hg
  apply faithful
  change (FiniteOscillator.CM.projection (g * h), FiniteOscillator.CM.action (g * h)) = (FiniteOscillator.CM.projection (h * g), FiniteOscillator.CM.action (h * g))
  apply Prod.ext
  · simp only [map_mul, hg, one_mul, mul_one]
  · apply LinearEquiv.ext
    intro f
    change FiniteOscillator.CM.action g (FiniteOscillator.CM.action h f) = FiniteOscillator.CM.action h (FiniteOscillator.CM.action g f)
    rw [hc, hc, map_smul]

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareNe.CM.OscillatorKernel

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareNe.CM.Group

/-! The intrinsic finite bare group generated by actual oscillator
commutators and the negative identity. Its genuine operator action is
constructed here. Surjectivity and two-fold kernel exactness remain
separate proof obligations. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator.CM

variable {I : Type*} [Fintype I]

theorem graph_neg (v : FiniteOscillator.CM.Phase (I := I)) (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    FiniteOscillator.CM.graph v (-f) (-h) ↔ FiniteOscillator.CM.graph v f h := by
  have he : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.Finite.character
      (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i)) (-f.val) =
      -(RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.Finite.character
        (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i)) f.val) := by
    funext x
    exact mul_neg _ _
  change -h.val = _ ↔ h.val = _
  rw [Submodule.coe_neg, he, neg_inj]

def minus : FiniteOscillator.CM.Oscillator (I := I) := by
  refine ⟨(1, LinearEquiv.neg ℂ), ?_⟩
  constructor
  · intro f h
    change FiniteOscillator.CM.integralPairing (-f) (-h) = FiniteOscillator.CM.integralPairing f h
    simp [FiniteOscillator.CM.integralPairing]
  · intro v f h
    change FiniteOscillator.CM.graph v f h ↔ FiniteOscillator.CM.graph (FiniteOscillator.CM.phaseAction 1 v) (-f) (-h)
    rw [FiniteOscillator.CM.phaseAction_one, graph_neg]

theorem project_minus : FiniteOscillator.CM.projection (minus (I := I)) = 1 := rfl

theorem action_minus (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : FiniteOscillator.CM.action minus f = -f := rfl

theorem minus_ne_one : minus (I := I) ≠ 1 := by
  intro he
  have h := congrArg (fun g : FiniteOscillator.CM.Oscillator (I := I) => (FiniteOscillator.CM.action g RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralTestFunction).val 0) he
  rw [action_minus, map_one] at h
  change -RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator (0 : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) = RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator (0 : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) at h
  rw [RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralIndicator_of_mem RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.integralVectors.zero_mem] at h
  norm_num at h

theorem minus_central (g : FiniteOscillator.CM.Oscillator (I := I)) : Commute minus g :=
  OscillatorKernel.kernel_central minus project_minus g

def bareSubgroup : Subgroup (FiniteOscillator.CM.Oscillator (I := I)) :=
  Subgroup.closure (commutatorSet (FiniteOscillator.CM.Oscillator (I := I)) ∪ {minus})

abbrev BareGroup := bareSubgroup (I := I)

def bareProjection : BareGroup (I := I) →* RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf := FiniteOscillator.CM.projection.comp bareSubgroup.subtype

def bareAction : BareGroup (I := I) →* (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :=
  FiniteOscillator.CM.action.comp bareSubgroup.subtype

def negOne : BareGroup (I := I) :=
  ⟨minus, Subgroup.subset_closure (Or.inr rfl)⟩

theorem negOne_ne_one : negOne (I := I) ≠ 1 := by
  intro he
  exact minus_ne_one (congrArg Subtype.val he)

theorem genuine (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : bareAction negOne f = -f := action_minus f

theorem project_negOne : bareProjection (negOne (I := I)) = 1 := project_minus

theorem unitary (g : BareGroup (I := I)) (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    FiniteOscillator.CM.integralPairing (bareAction g f) (bareAction g h) = FiniteOscillator.CM.integralPairing f h :=
  FiniteOscillator.CM.unitary g.val f h

theorem intertwines (g : BareGroup (I := I)) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.IntertwinesHeisenberg Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)
      (bareProjection g) (bareAction g) := FiniteOscillator.CM.intertwines g.val

theorem faithful : Function.Injective (fun g : BareGroup (I := I) => (bareProjection g, bareAction g)) := by
  intro g h he
  exact Subtype.ext (OscillatorKernel.faithful he)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareNe.CM.Group

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareNe.CM.Normal

/-! Normality of the intrinsic finite bare group follows from its
commutator generators and the actual central negative identity. -/

open scoped Classical commutatorElement
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareNe.CM.Group

variable {I : Type*} [Fintype I]

theorem minus_conjugation (g : FiniteOscillator.CM.Oscillator (I := I)) : g * Group.minus * g⁻¹ = Group.minus := by
  rw [← (Group.minus_central g).eq, mul_assoc, mul_inv_cancel, mul_one]

instance bare_normal : (Group.bareSubgroup (I := I)).Normal where
  conj_mem z hz g := by
    induction hz using Subgroup.closure_induction with
    | mem z hz =>
        rcases hz with hz | hz
        · obtain ⟨u, v, rfl⟩ := hz
          apply Subgroup.subset_closure
          left
          exact ⟨g * u * g⁻¹, g * v * g⁻¹, (conjugate_commutatorElement u v g).symm⟩
        · obtain rfl := hz
          rw [minus_conjugation]
          exact Subgroup.subset_closure (Or.inr rfl)
    | one => simp
    | mul a b _ _ ha hb =>
        rw [← conj_mul]
        exact Group.bareSubgroup.mul_mem ha hb
    | inv a _ ha =>
        rw [← conj_inv]
        exact Group.bareSubgroup.inv_mem ha

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareNe.CM.Normal

end

end OAI
