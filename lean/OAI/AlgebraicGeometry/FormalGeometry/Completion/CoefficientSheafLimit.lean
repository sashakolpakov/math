import OAI.AlgebraicGeometry.FormalGeometry.Completion.CoefficientLimit
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf

/-! # Coefficient Sheaf Limit -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.CoefficientSheafLimit.Construction

noncomputable section

/-!
# Completion: the inverse-limit property on actual coefficient-sheaf sections

Finite transitions and integral reductions are the maps on continuous
functions. The inverse-limit reconstruction holds on every object of the
actual pro-étale site.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (ℓ : ℕ)

/-- Transition between finite continuous coefficient presheaves. -/
def continuousFiniteCoefficientTransition (m n : ℕ) (h : m ≤ n) :
    continuousMapPresheafAb (ZMod (ℓ ^ n)) ⟶ continuousMapPresheafAb (ZMod (ℓ ^ m)) where
  app U := AddCommGrpCat.ofHom {
    toFun f := ⟨fun x => ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) (f x),
      continuous_of_discreteTopology.comp f.continuous⟩
    map_zero' := by
      apply ContinuousMap.ext
      intro x
      exact map_zero (ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)))
    map_add' f g := by
      apply ContinuousMap.ext
      intro x
      exact map_add (ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m))) (f x) (g x) }
  naturality := by intros; rfl

/-- Transition between actual finite coefficient sheaves. -/
def finiteEllAdicTransition (m n : ℕ) (h : m ≤ n) (X : Scheme.{u}) :
    Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X ⟶ Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ m X where
  hom := Functor.whiskerRight
    (Functor.whiskerLeft (Scheme.ProEt.forget X ⋙ Over.forget _).op
      (continuousFiniteCoefficientTransition ℓ m n h)) AddCommGrpCat.uliftFunctor

variable [Fact ℓ.Prime] (X : Scheme.{u})

theorem finiteEllAdicReduction_transition (m n : ℕ) (h : m ≤ n) :
    Finite.CoefficientSheaf.Construction.finiteEllAdicReduction ℓ n X ≫ finiteEllAdicTransition ℓ m n h X =
      Finite.CoefficientSheaf.Construction.finiteEllAdicReduction ℓ m X := by
  ext U s
  change ULift.{u + 1} C(U.unop.left, ℤ_[ℓ]) at s
  apply ULift.ext
  apply ContinuousMap.ext
  intro t
  exact congrArg (fun f => f (s.down t)) (PadicInt.zmod_cast_comp_toZModPow m n h)

/-- Finite reductions detect equality of actual integral coefficient sections. -/
theorem integralCoefficientSections_ext (U : X.ProEtᵒᵖ)
    (a b : (ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X).obj.obj U)
    (h : ∀ n, (Finite.CoefficientSheaf.Construction.finiteEllAdicReduction ℓ n X).hom.app U a =
      (Finite.CoefficientSheaf.Construction.finiteEllAdicReduction ℓ n X).hom.app U b) : a = b := by
  change ULift.{u + 1} C(U.unop.left, ℤ_[ℓ]) at a b
  apply ULift.ext
  apply ContinuousMap.ext
  intro t
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  exact congrArg (fun z : ULift.{u + 1} C(U.unop.left, ZMod (ℓ ^ n)) => z.down t) (h n)

/-- Every compatible family of finite sections comes from one integral section. -/
theorem integralCoefficientSections_existsUnique (U : X.ProEtᵒᵖ)
    (s : ∀ n, (Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).obj.obj U)
    (hs : ∀ m n (h : m ≤ n),
      (finiteEllAdicTransition ℓ m n h X).hom.app U (s n) = s m) :
    ∃! a : (ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X).obj.obj U,
      ∀ n, (Finite.CoefficientSheaf.Construction.finiteEllAdicReduction ℓ n X).hom.app U a = s n := by
  let f (n : ℕ) : C(U.unop.left, ZMod (ℓ ^ n)) :=
    (show ULift.{u + 1} C(U.unop.left, ZMod (ℓ ^ n)) from s n).down
  have hf : ∀ m n (h : m ≤ n) t,
      ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) (f n t) = f m t := by
    intro m n h t
    exact congrArg (fun z : ULift.{u + 1} C(U.unop.left, ZMod (ℓ ^ m)) => z.down t) (hs m n h)
  obtain ⟨g, hg, _⟩ := CoefficientLimit.Construction.continuousMap_existsUnique_of_coherentFinite ℓ f hf
  have hred (n : ℕ) : (Finite.CoefficientSheaf.Construction.finiteEllAdicReduction ℓ n X).hom.app U (ULift.up g) = s n := by
    apply ULift.ext
    exact ContinuousMap.ext (hg n)
  refine ⟨ULift.up g, hred, ?_⟩
  intro a ha
  exact integralCoefficientSections_ext ℓ X U a (ULift.up g)
    (fun n => (ha n).trans (hred n).symm)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.CoefficientSheafLimit.Construction
