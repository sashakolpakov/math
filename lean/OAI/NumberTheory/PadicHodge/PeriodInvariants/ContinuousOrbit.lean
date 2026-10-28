import Mathlib

/-! # Continuous Orbit -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.PeriodInvariants.ContinuousOrbit

/-! # Continuous orbits of a jointly continuous family -/

theorem continuous {G V : Type*} [TopologicalSpace G] [TopologicalSpace V]
    (f : G → V → V) (hf : Continuous (fun z : G × V => f z.1 z.2)) (x : V) :
    Continuous (fun g => f g x) :=
  hf.comp (continuous_id.prodMk continuous_const)

end NumberTheory.PadicHodge.PeriodInvariants.ContinuousOrbit

namespace NumberTheory.PadicHodge.PeriodInvariants.ContinuousOrbit.PiRepresentation

/-! # Coordinatewise continuous representations and coinduced function coordinates -/

variable {R G V I : Type*} [Ring R] [TopologicalSpace R] [Monoid G]
  [AddCommGroup V] [Module R V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul R V]

def piRepresentation (ρ : ContRepresentation R G V) : ContRepresentation R G (I → V) where
  toMonoidHom.toFun g := ContinuousLinearMap.pi (fun i => (ρ g).comp (ContinuousLinearMap.proj i))
  toMonoidHom.map_one' := by
    apply ContinuousLinearMap.ext
    intro v
    funext i
    exact DFunLike.congr_fun (map_one ρ) (v i)
  toMonoidHom.map_mul' g h := by
    apply ContinuousLinearMap.ext
    intro v
    funext i
    exact DFunLike.congr_fun (map_mul ρ g h) (v i)

variable [TopologicalSpace G]

omit [TopologicalSpace R] [ContinuousSMul R V] in
theorem pi_joint (ρ : ContRepresentation R G V)
    (hρ : Continuous (fun z : G × V => ρ z.1 z.2)) :
    Continuous (fun z : G × (I → V) => piRepresentation ρ z.1 z.2) := by
  apply continuous_pi
  intro i
  have h : Continuous (fun z : G × (I → V) => (z.1, z.2 i)) :=
    continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)
  exact hρ.comp h

variable [LocallyCompactSpace G]

def coindPiEquiv : C(G, I → V) ≃L[R] (I → C(G, V)) where
  toFun f i := (ContinuousMap.eval i).comp f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := ContinuousMap.pi
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi (fun i => ContinuousMap.continuous_postcomp (ContinuousMap.eval i))
  continuous_invFun := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply continuous_pi
    intro i
    exact continuous_eval.comp (((continuous_apply i).comp continuous_fst).prodMk continuous_snd)

end NumberTheory.PadicHodge.PeriodInvariants.ContinuousOrbit.PiRepresentation

end

end OAI
