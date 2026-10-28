import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Principal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.PDLogarithmicBoundary
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechLargeTop

/-! # Residue Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResidueClass

noncomputable section

/-! The literal residue cocycle in the coefficient universe of the
original injective resolution. Its finite-log boundary proves independence
of the chosen lifts of the residual parameters. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "Q" => Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmallFrame.functor p k n X Y f hp) U
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Principal.Comparison.source p k n X Y f hp U

local instance coefficient_limits : HasLimitsOfSize.{0,0} (ModuleCat.{2} R) :=
  ModuleCat.hasLimitsOfSize.{0,0,2,1}

local instance coefficient_colimits : HasColimitsOfSize.{0,0} (ModuleCat.{2} R) :=
  ModuleCat.hasColimitsOfSize.{2,1,0,0} R

variable (g : ℕ) (a : Fin g → Γ(X.left, U.val))

def form : ((K).X g).obj (op (Supported.PDComplex.topCoefficient p k Y Q g a)) :=
  ⟨⟨Supported.PDComplex.logarithmicForm p k Y Q g a⟩⟩

omit [IsProper X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem form_closed : ((K).d g (g + 1)).app (op (Supported.PDComplex.topCoefficient p k Y Q g a))
    (form p k n X Y f hp U g a) = 0 :=
  congrArg (fun z => ULift.up.{2,1} (ULift.up.{1,0} z))
    (Supported.PDComplex.logarithmicForm_closed p k Y Q g a)

def residueClass := AugmentedOrdered.CechLargeTop.topTotalClass
  (Supported.PDComplex.family p k Y Q g a) K g (by simp) g
  (form p k n X Y f hp U g a) (form_closed p k n X Y f hp U g a)

variable (b : Fin g → Γ(X.left, U.val))
  (hab : ∀ i,
    ((SmallFrame.functor p k n X Y f hp).obj U).thickening.reduction (b i) =
      ((SmallFrame.functor p k n X Y f hp).obj U).thickening.reduction (a i))

def changedForm : ((K).X g).obj (op (Supported.PDComplex.topCoefficient p k Y Q g a)) :=
  ⟨⟨Supported.PDLiftIndependence.Complex.changedLogarithmicForm p k Y Q g a b hab⟩⟩

omit [IsProper X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem changedForm_closed : ((K).d g (g + 1)).app
    (op (Supported.PDComplex.topCoefficient p k Y Q g a))
      (changedForm p k n X Y f hp U g a b hab) = 0 :=
  congrArg (fun z => ULift.up.{2,1} (ULift.up.{1,0} z))
    (Supported.PDLiftIndependence.Complex.changedLogarithmicForm_closed p k Y Q g a b hab)

def changedResidueClass := AugmentedOrdered.CechLargeTop.topTotalClass
  (Supported.PDComplex.family p k Y Q g a) K g (by simp) g
  (changedForm p k n X Y f hp U g a b hab) (changedForm_closed p k n X Y f hp U g a b hab)

omit [IsProper X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem changedResidueClass_eq : changedResidueClass p k n X Y f hp U g a b hab =
    residueClass p k n X Y f hp U g a := by
  cases g with
  | zero => rfl
  | succ d =>
      obtain ⟨r, hr⟩ := (Q).thickening.p_nilpotent
      have hN := Supported.PDLogarithmicBoundary.Complex.factorial_zero_of_prime_power p k Y Q d a r hr
      have hη := Supported.PDLogarithmicBoundary.Complex.primitiveForm_differential p k Y Q d a b hab (r * p) hN
      apply AugmentedOrdered.CechLargeTop.topTotalClass_eq
        (Supported.PDComplex.family p k Y Q (d + 1) a) K (d + 1) (by simp) d
        (changedForm p k n X Y f hp U (d + 1) a b hab)
        (form p k n X Y f hp U (d + 1) a)
        (changedForm_closed p k n X Y f hp U (d + 1) a b hab)
        (form_closed p k n X Y f hp U (d + 1) a)
        ⟨⟨Supported.PDLogarithmicBoundary.Complex.primitiveForm p k Y Q d a b hab (r * p)⟩⟩
      exact congrArg (fun z => ULift.up.{2,1} (ULift.up.{1,0} z)) hη

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResidueClass
