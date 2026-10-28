import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FourierHeisenberg
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.Plancherel

/-! # Finite Oscillator -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator.CM

noncomputable section

/-! The finite oscillator group is constructed from actual symplectic
matrices and unitary Heisenberg intertwiners on finite Schwartz functions.
No double-cover exactness or rational splitting is assumed here. -/

open scoped Classical _root_.Matrix
open _root_.MeasureTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure.CM

variable {I : Type*} [Fintype I]

abbrev Phase := (I ⊕ I) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf

def phaseAction (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : Phase (I := I)) : Phase (I := I) := g.val *ᵥ v

theorem phaseAction_one (v : Phase (I := I)) : phaseAction 1 v = v := Matrix.one_mulVec v

theorem phaseAction_mul (g h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : Phase (I := I)) :
    phaseAction (g * h) v = phaseAction g (phaseAction h v) :=
  (Matrix.mulVec_mulVec v g.val h.val).symm

theorem phaseAction_inv (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : Phase (I := I)) :
    phaseAction g (phaseAction g⁻¹ v) = v := by
  rw [← phaseAction_mul, mul_inv_cancel, phaseAction_one]

def graph (v : Phase (I := I)) (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : Prop :=
  h.val = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.Finite.character
    (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i)) f.val

omit [Fintype I] in
theorem phase_reconstruct (v : Phase (I := I)) :
    Sum.elim (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i)) = v := by
  funext i
  cases i <;> rfl

theorem graph_of_intertwines (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (T : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)
    (hT : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.IntertwinesHeisenberg Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) g T)
    (v : Phase (I := I)) (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    graph v f h ↔ graph (phaseAction g v) (T f) (T h) := by
  have hfwd (f' h' : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (hh : graph v f' h') :
      graph (phaseAction g v) (T f') (T h') := by
    have he := funext (hT (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i))
      f' h' (congrFun hh))
    rw [phase_reconstruct] at he
    exact he
  refine ⟨hfwd f h, fun hh => ?_⟩
  let k := FourierHeisenberg.CM.operator
    (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i)) f
  have hk : graph v f k := rfl
  have he : T h = T k := Subtype.ext (hh.trans (hfwd f k hk).symm)
  exact congrArg Subtype.val (T.injective he)

def integralPairing (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : ℂ :=
  ∫ x, f.val x * star (h.val x) ∂(Constructed.FiniteMeasure.CM.measure I)

def oscillatorSubgroup :
    Subgroup (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf × (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)) where
  carrier := {a |
    (∀ f h, integralPairing (a.2 f) (a.2 h) = integralPairing f h) ∧
    ∀ v f h, graph v f h ↔ graph (phaseAction a.1 v) (a.2 f) (a.2 h)}
  one_mem' := by
    constructor
    · intro f h; rfl
    · intro v f h
      change graph v f h ↔ graph (phaseAction 1 v) f h
      rw [phaseAction_one]
  mul_mem' := by
    intro a b ha hb
    constructor
    · intro f h
      change integralPairing (a.2 (b.2 f)) (a.2 (b.2 h)) = integralPairing f h
      rw [ha.1, hb.1]
    · intro v f h
      change graph v f h ↔ graph (phaseAction (a.1 * b.1) v)
        (a.2 (b.2 f)) (a.2 (b.2 h))
      rw [phaseAction_mul]
      exact (hb.2 v f h).trans (ha.2 _ _ _)
  inv_mem' := by
    intro a ha
    constructor
    · intro f h
      have he := ha.1 (a.2.symm f) (a.2.symm h)
      simpa using he.symm
    · intro v f h
      change graph v f h ↔ graph (phaseAction a.1⁻¹ v) (a.2.symm f) (a.2.symm h)
      have he := ha.2 (phaseAction a.1⁻¹ v) (a.2.symm f) (a.2.symm h)
      simpa only [phaseAction_inv, LinearEquiv.apply_symm_apply] using he.symm

abbrev Oscillator := oscillatorSubgroup (I := I)

def projection : Oscillator (I := I) →* RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf :=
  (MonoidHom.fst _ _).comp oscillatorSubgroup.subtype

def action : Oscillator (I := I) →* (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :=
  (MonoidHom.snd _ _).comp oscillatorSubgroup.subtype

theorem unitary (g : Oscillator (I := I)) (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    integralPairing (action g f) (action g h) = integralPairing f h := g.property.1 f h

theorem intertwines (g : Oscillator (I := I)) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.IntertwinesHeisenberg Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)
      (projection g) (action g) := by
  intro p q f h hh x
  exact congrFun ((g.property.2 (Sum.elim p q) f h).mp (funext hh)) x

def fourierOscillator : Oscillator (I := I) := by
  refine ⟨(FourierHeisenberg.CM.weyl, FourierHeisenberg.CM.Equiv.fourierEquiv), ?_⟩
  exact ⟨Plancherel.CM.unitary,
    graph_of_intertwines _ _ FourierHeisenberg.CM.intertwines⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator.CM
