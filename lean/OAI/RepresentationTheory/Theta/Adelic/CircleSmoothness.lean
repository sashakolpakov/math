import OAI.RepresentationTheory.Weil.UnitarySplitting.Weak
import OAI.RepresentationTheory.Weil.AdelicSplitting.Vacuum

/-! # Circle Smoothness -/

namespace OAI.RepresentationTheory.Theta.Adelic.CircleSmoothness

noncomputable section

/-!
# The circle extension obstructs the ambient smoothness premise of AdelicTheta

The committed conditional theorem is preserved. Its premise `hWeilSmooth`
asks for open vector stabilizers in the entire finite circle extension.
That premise cannot hold for the actual oscillator action and its strong
L² topology: the continuous circle scalars fix a nonzero vector only at 1.

The results below use the actual LocalWeil/UnitarySplitting/AdelicSplitting constructions. In particular,
the finite vacuum gives an explicit nonzero Schwartz vector at every finite
place. No splitting theorem or compatibility premise is used. Smoothness
after restriction to a special-unitary splitting is a different property;
these results do not contradict the manuscript's assertion of that property.
-/

open OAI.RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction
open scoped _root_.NumberField

theorem circle_identity_not_open : ¬ IsOpen ({1} : Set Circle) := by
  intro hopen
  have hclopen : IsClopen ({1} : Set Circle) := ⟨isClosed_singleton, hopen⟩
  rcases isClopen_iff.mp hclopen with hempty | huniv
  · have h : (1 : Circle) ∈ (∅ : Set Circle) := by
      rw [← hempty]
      exact Set.mem_singleton 1
    exact h
  · have h : (-1 : Circle) = 1 := by
      apply Set.mem_singleton_iff.mp
      rw [huniv]
      exact Set.mem_univ _
    have hc := congrArg (fun z : Circle => (z : ℂ)) h
    norm_num at hc

/-- A continuous circle acting by its usual nontrivial scalar action
prevents every nonzero vector stabilizer from being open. -/
theorem stabilizer_not_open_of_circle_scalars
    {G S : Type*} [Group G] [TopologicalSpace G]
    [AddCommGroup S] [Module ℂ S]
    (scalars : Circle →ₜ* G)
    (representation : G →* (S ≃ₗ[ℂ] S))
    (scalar_action : ∀ (z : Circle) (f : S),
      representation (scalars z) f = (z : ℂ) • f)
    (f : S) (hf : f ≠ 0) :
    ¬ IsOpen {g : G | representation g f = f} := by
  intro hopen
  have hpre : scalars ⁻¹' {g : G | representation g f = f} =
      ({1} : Set Circle) := by
    ext z
    change representation (scalars z) f = f ↔ z = 1
    rw [scalar_action]
    constructor
    · intro h
      apply Circle.coe_injective
      apply smul_left_injective ℂ hf
      simpa only [Circle.coe_one, one_smul] using h
    · rintro rfl
      simp
  exact circle_identity_not_open (hpre ▸ hopen.preimage scalars.continuous)

section Local

variable (k : Type) [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    (N : ℕ) (ψ : AddChar k ℂ)

/-- Continuity is proved for AdelicSplitting's actual strong-L² topology, using the
checked UnitarySplitting embedding of the same Schwartz space into L². -/
theorem localScalar_continuous : Continuous (Weil.AdelicSplitting.Oscillator.Construction.localScalar k N ψ) := by
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · exact continuous_const
  · apply Continuous.prodMk
    · apply continuous_pi
      intro p
      change Continuous (fun z : Circle =>
        Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.l2Energy k N ((z : ℂ) • p.1 - p.2)))
      simp_rw [← Weil.UnitarySplitting.Weak.Construction.testToL2_norm, map_sub, map_smul]
      fun_prop
    · apply continuous_pi
      intro p
      change Continuous (fun z : Circle =>
        Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.l2Energy k N ((↑(z⁻¹) : ℂ) • p.1 - p.2)))
      simp_rw [← Weil.UnitarySplitting.Weak.Construction.testToL2_norm, map_sub, map_smul]
      fun_prop

/-- The actual AdelicSplitting local oscillator representation is not smooth as a
representation of the circle extension, on any nonzero test vector. -/
theorem local_stabilizer_not_open
    (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (hf : f ≠ 0) :
    ¬ IsOpen {g : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ | Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ g f = f} :=
  stabilizer_not_open_of_circle_scalars
    ⟨Weil.AdelicSplitting.Oscillator.Construction.localScalar k N ψ, localScalar_continuous k N ψ⟩
    (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ) (Weil.AdelicSplitting.Oscillator.Construction.localOperator_scalar k N ψ) f hf

end Local

/-- The same obstruction holds directly in UnitarySplitting's tensor-space circle
extension, with its constructed oscillator representation. -/
theorem stabilizer_not_open
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [LocallyCompactSpace F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F]
    {m n : ℕ} (σ : E ≃ₐ[F] E)
    (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (c : Weil.UnitarySplitting.Oscillator.Construction.SymplecticFrame σ H K)
    (ψ : AddChar F ℂ) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n)) (hf : f ≠ 0) :
    ¬ IsOpen {g : Weil.UnitarySplitting.Oscillator.Construction.CircleExtension σ H K c ψ |
      Weil.UnitarySplitting.Oscillator.Construction.oscillatorRepresentation σ H K c ψ g f = f} :=
  stabilizer_not_open_of_circle_scalars
    ⟨Weil.UnitarySplitting.Oscillator.Construction.circleScalar σ H K c ψ,
      Weil.UnitarySplitting.Weak.Construction.circleScalar_continuous σ H K c ψ⟩
    (Weil.UnitarySplitting.Oscillator.Construction.oscillatorRepresentation σ H K c ψ)
    (fun _ _ => rfl) f hf

local instance finiteMeasurableSpace
    (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) :=
  Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionMeasurableSpace F (.inr v)

local instance finiteBorelSpace
    (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) :=
  Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionBorelSpace F (.inr v)

/-- A concrete finite-place counterexample: the standard characteristic
function of the integral position lattice has a non-open stabilizer. -/
theorem finite_vacuum_stabilizer_not_open
    (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (N : ℕ) (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) :
    ¬ IsOpen {g : Weil.AdelicSplitting.Vacuum.Construction.CoverAt F N ψ (.inr v) |
      Weil.AdelicSplitting.Oscillator.Construction.localOperator (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N
        (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v)) g (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) =
          Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v} := by
  apply local_stabilizer_not_open
  intro hzero
  have h := congrArg
    (fun f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N => f.val 0) hzero
  have hone := Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum_zero F N v
  change (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val 0 = 0 at h
  exact one_ne_zero (hone.symm.trans h)

/-- The universal ambient smoothness premise used by the committed AdelicTheta
model is false for the actual finite local circle extension. -/
theorem actual_finite_circle_action_not_smooth
    (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (N : ℕ) (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) :
    ¬ (∀ f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N,
      IsOpen {g : Weil.AdelicSplitting.Vacuum.Construction.CoverAt F N ψ (.inr v) |
        Weil.AdelicSplitting.Oscillator.Construction.localOperator (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N
          (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v)) g f = f}) := by
  intro hsmooth
  exact finite_vacuum_stabilizer_not_open F v N ψ (hsmooth (Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v))

end

end OAI.RepresentationTheory.Theta.Adelic.CircleSmoothness
