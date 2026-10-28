import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SmoothFunctionAction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.OscillatorHomAssembly

/-! # Oscillator Closure -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.OscillatorClosure.CM

/-! The unitary and Heisenberg identities of a smooth finite Schwartz
representation extend from a subgroup to its topological closure. -/

open scoped Classical _root_.Matrix _root_.Topology
open _root_.Matrix

variable {I G : Type*} [Fintype I] [DecidableEq I]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : G →* (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I))
  (hρ : ∀ f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I, IsOpen {g : G | ρ g f = f})

include hρ in
omit [DecidableEq I] in
theorem evaluation (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    Continuous (fun p : G × (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) => (ρ p.1 f).val p.2) :=
  SmoothFunctionAction.CM.evaluation ρ hρ (fun f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I => f.val)
    (fun f => ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff f.val).mp f.property).1.continuous) f

include hρ in
omit [DecidableEq I] in
theorem heisenberg_value (p q : G → (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) (hp : Continuous p) (hq : Continuous q)
    (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    Continuous (fun g : G => (Finite.FourierHeisenberg.CM.operator (p g) (q g) (ρ g f)).val x) := by
  change Continuous (fun g : G => Constructed.AdelicCharacter.CM.Finite.character
    (∑ i, p g i * (x i - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * q g i)) *
      (ρ g f).val (fun i => x i - q g i))
  apply (Constructed.AdelicCharacter.CM.Finite.character_continuous.comp ?_).mul
    ((evaluation ρ hρ f).comp (continuous_id.prodMk (continuous_const.sub hq)))
  exact continuous_finsetSum Finset.univ (fun i _ =>
    ((continuous_apply i).comp hp).mul
      (continuous_const.sub (continuous_const.mul ((continuous_apply i).comp hq))))

include hρ in
omit [DecidableEq I] in
theorem unitary_closed : IsClosed {g : G | ∀ f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I,
    Finite.FiniteOscillator.CM.integralPairing (ρ g f) (ρ g h) = Finite.FiniteOscillator.CM.integralPairing f h} := by
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro f
  apply isClosed_iInter
  intro h
  exact ((SmoothFunctionAction.CM.orbit ρ hρ f).comp₂
    (SmoothFunctionAction.CM.orbit ρ hρ h) Finite.FiniteOscillator.CM.integralPairing).isClosed_fiber _

variable (s : G →* RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
  (hs : ∀ v : (I ⊕ I) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf, Continuous (fun g : G => (s g).val *ᵥ v))

include hρ hs in
theorem point_closed (v : (I ⊕ I) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    IsClosed {g : G |
      (ρ g (Finite.FourierHeisenberg.CM.operator (fun i => v (.inl i)) (fun i => v (.inr i)) f)).val x =
        (Finite.FourierHeisenberg.CM.operator (fun i => ((s g).val *ᵥ v) (.inl i))
          (fun i => ((s g).val *ᵥ v) (.inr i)) (ρ g f)).val x} := by
  have hlp : Continuous (fun a : (I ⊕ I) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => fun i : I => a (.inl i)) :=
    continuous_pi (fun i : I => (continuous_apply (Sum.inl i : I ⊕ I) :
      Continuous (fun a : (I ⊕ I) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => a (.inl i))))
  have hrp : Continuous (fun a : (I ⊕ I) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => fun i : I => a (.inr i)) :=
    continuous_pi (fun i : I => (continuous_apply (Sum.inr i : I ⊕ I) :
      Continuous (fun a : (I ⊕ I) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => a (.inr i))))
  have hp : Continuous (fun g : G => fun i : I => ((s g).val *ᵥ v) (.inl i)) := hlp.comp (hs v)
  have hq : Continuous (fun g : G => fun i : I => ((s g).val *ᵥ v) (.inr i)) := hrp.comp (hs v)
  have hl := (SmoothFunctionAction.CM.orbit ρ hρ
    (Finite.FourierHeisenberg.CM.operator (fun i => v (.inl i)) (fun i => v (.inr i)) f)).comp
      (fun φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I => φ.val x)
  have hr := heisenberg_value ρ hρ
    (fun g : G => fun i => ((s g).val *ᵥ v) (.inl i))
    (fun g : G => fun i => ((s g).val *ᵥ v) (.inr i)) hp hq f x
  exact isClosed_eq hl.continuous hr

include hρ hs in
theorem covariance_closed : IsClosed {g : G | ∀ (v : (I ⊕ I) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I),
    ρ g (Finite.FourierHeisenberg.CM.operator (fun i => v (.inl i)) (fun i => v (.inr i)) f) =
      Finite.FourierHeisenberg.CM.operator (fun i => ((s g).val *ᵥ v) (.inl i))
        (fun i => ((s g).val *ᵥ v) (.inr i)) (ρ g f)} := by
  have he : (fun g : G => ∀ (v : (I ⊕ I) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I),
      ρ g (Finite.FourierHeisenberg.CM.operator (fun i => v (.inl i)) (fun i => v (.inr i)) f) =
        Finite.FourierHeisenberg.CM.operator (fun i => ((s g).val *ᵥ v) (.inl i))
          (fun i => ((s g).val *ᵥ v) (.inr i)) (ρ g f)) =
    (fun g : G => ∀ (v : (I ⊕ I) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf),
      (ρ g (Finite.FourierHeisenberg.CM.operator (fun i => v (.inl i)) (fun i => v (.inr i)) f)).val x =
        (Finite.FourierHeisenberg.CM.operator (fun i => ((s g).val *ᵥ v) (.inl i))
          (fun i => ((s g).val *ᵥ v) (.inr i)) (ρ g f)).val x) := by
    funext g
    apply propext
    constructor
    · intro h v f x
      exact congrArg (fun a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I => a.val x) (h v f)
    · intro h v f
      exact Subtype.ext (funext (h v f))
  rw [he]
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro v
  apply isClosed_iInter
  intro f
  apply isClosed_iInter
  intro x
  exact point_closed ρ hρ s hs v f x

include hρ hs in
theorem on_closure (K : Subgroup G)
    (hu : ∀ g ∈ K, ∀ f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I,
      Finite.FiniteOscillator.CM.integralPairing (ρ g f) (ρ g h) = Finite.FiniteOscillator.CM.integralPairing f h)
    (hc : ∀ g ∈ K, ∀ (v : (I ⊕ I) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I),
      ρ g (Finite.FourierHeisenberg.CM.operator (fun i => v (.inl i)) (fun i => v (.inr i)) f) =
        Finite.FourierHeisenberg.CM.operator (fun i => ((s g).val *ᵥ v) (.inl i))
          (fun i => ((s g).val *ᵥ v) (.inr i)) (ρ g f))
    (g : G) (hg : g ∈ K.topologicalClosure) :
    (∀ f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I, Finite.FiniteOscillator.CM.integralPairing (ρ g f) (ρ g h) =
      Finite.FiniteOscillator.CM.integralPairing f h) ∧
    (∀ (v : (I ⊕ I) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I),
      ρ g (Finite.FourierHeisenberg.CM.operator (fun i => v (.inl i)) (fun i => v (.inr i)) f) =
        Finite.FourierHeisenberg.CM.operator (fun i => ((s g).val *ᵥ v) (.inl i))
          (fun i => ((s g).val *ᵥ v) (.inr i)) (ρ g f)) :=
  ⟨closure_minimal hu (unitary_closed ρ hρ) hg,
    closure_minimal hc (covariance_closed ρ hρ s hs) hg⟩

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.OscillatorClosure.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.OscillatorClosure.CM.Rational

/-! Apply oscillator closure directly from the actual rational homomorphism. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable {I G R : Type*} [Fintype I] [DecidableEq I]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group R]
  (ρ : G →* (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I))
  (hρ : ∀ f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I, IsOpen {g : G | ρ g f = f})
  (s : G →* RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hs : ∀ v : (I ⊕ I) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf, Continuous (fun g : G => (s g).val *ᵥ v))
  (r : R →* G)

include hρ hs in
theorem apply (hu : ∀ a : R, ∀ f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I,
      Finite.FiniteOscillator.CM.integralPairing (ρ (r a) f) (ρ (r a) h) = Finite.FiniteOscillator.CM.integralPairing f h)
    (hc : ∀ a : R, ∀ (v : (I ⊕ I) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I),
      ρ (r a) (Finite.FourierHeisenberg.CM.operator (fun i => v (.inl i)) (fun i => v (.inr i)) f) =
        Finite.FourierHeisenberg.CM.operator (fun i => ((s (r a)).val *ᵥ v) (.inl i))
          (fun i => ((s (r a)).val *ᵥ v) (.inr i)) (ρ (r a) f))
    (g : G) (hg : g ∈ r.range.topologicalClosure) :
    (∀ f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I, Finite.FiniteOscillator.CM.integralPairing (ρ g f) (ρ g h) =
      Finite.FiniteOscillator.CM.integralPairing f h) ∧
    (∀ (v : (I ⊕ I) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I),
      ρ g (Finite.FourierHeisenberg.CM.operator (fun i => v (.inl i)) (fun i => v (.inr i)) f) =
        Finite.FourierHeisenberg.CM.operator (fun i => ((s g).val *ᵥ v) (.inl i))
          (fun i => ((s g).val *ᵥ v) (.inr i)) (ρ g f)) :=
  on_closure ρ hρ s hs r.range
    (by rintro _ ⟨a, rfl⟩; exact hu a) (by rintro _ ⟨a, rfl⟩; exact hc a) g hg

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.OscillatorClosure.CM.Rational

end

end OAI
