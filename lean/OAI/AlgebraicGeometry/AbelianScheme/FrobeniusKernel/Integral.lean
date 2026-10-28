import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Has
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Integral -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Integral.Construction

noncomputable section

/-!
The integral and special-fiber objects underlying FrobeniusKernel. The coefficient
splittings are actual ring isomorphisms for O_E/(q^n), and the PEL family
comes from IntegralModel's actual integral spread, including its generic-fiber
identification. No kernel-operator or Frobenius conclusion is a field.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
variable (iota : E →+* K) (κ : K →+* ℂ)
variable (M : Over (Spec (.of K))) (U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M)
variable (B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ)
variable (q : ℕ) [Fact q.Prime]

/-- Native integral PEL data at the chosen completely split prime.
The local coefficient isomorphisms specify the chosen split places, rather
than replacing finite flat subgroup schemes by constant groups. -/
structure SplitPELReduction where
  integral : PELModuli.IntegralModel.PEL.Has.IntegralPELSpread P iota κ N M U B
  residue : B.R →+* ZMod q
  smooth : Smooth integral.toOver.hom
  proper : IsProper integral.toOver.hom
  levelPrimeToQ : Nat.Coprime q N
  polarizationPrimeToQ : Nat.Coprime q ((∏ i, P.polarizationType i) ^ 2)
  active : Fin s
  splitCoefficients : ∀ n : ℕ,
    (NumberField.RingOfIntegers E ⧸
      Ideal.span ({(q ^ n : NumberField.RingOfIntegers E)} :
        Set (NumberField.RingOfIntegers E))) ≃+*
      ((Fin s × Bool) → ZMod (q ^ n))
  compatible : ∀ (n : ℕ) (a : NumberField.RingOfIntegers E) (v : Fin s × Bool),
    ZMod.castHom (show q ^ n ∣ q ^ (n + 1) by
      rw [pow_succ]
      exact dvd_mul_right _ _) (ZMod (q ^ n))
      (splitCoefficients (n + 1) (Ideal.Quotient.mk _ a) v) =
        splitCoefficients n (Ideal.Quotient.mk _ a) v
  conjugation : ∀ (n : ℕ) (a : NumberField.RingOfIntegers E) (v : Fin s) (b : Bool),
    splitCoefficients n (Ideal.Quotient.mk _
      (NumberField.IsCMField.ringOfIntegersComplexConj E a)) (v, b) =
    splitCoefficients n (Ideal.Quotient.mk _ a) (v, !b)

attribute [instance] SplitPELReduction.smooth SplitPELReduction.proper

namespace SplitPELReduction

variable {P iota κ M U B q}
variable (D : SplitPELReduction P iota κ M U B q)

/-- The residue-field morphism from the literal integral coefficient ring. -/
def specialBase : Spec (.of (ZMod q)) ⟶ B.base :=
  Spec.map (CommRingCat.ofHom D.residue)

/-- Reduction of the actual moduli scheme. -/
def specialFiber : Over (Spec (.of (ZMod q))) :=
  (Over.pullback D.specialBase).obj D.integral.toOver

def specialProjection : D.specialFiber.left ⟶ D.integral.toOver.left :=
  pullback.fst D.integral.toOver.hom D.specialBase

theorem specialFiber_square :
    IsPullback D.specialProjection D.specialFiber.hom
      D.integral.toOver.hom D.specialBase :=
  IsPullback.of_hasPullback _ _

instance specialFiber_smooth : Smooth D.specialFiber.hom :=
  inferInstanceAs (Smooth (pullback.snd D.integral.toOver.hom D.specialBase))

instance specialFiber_proper : IsProper D.specialFiber.hom :=
  inferInstanceAs (IsProper (pullback.snd D.integral.toOver.hom D.specialBase))

/-- The special-fiber abelian scheme is constructed by base change. -/
def abelian : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) D.specialFiber.left :=
  D.integral.universal.data.polarized.abelian.pullback D.specialProjection

/-- The complete polarized and marked family is actually reduced, including
the dual abelian scheme and the Poincare data defining its polarization. -/
def polarized :
    AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N D.specialFiber.left :=
  D.integral.universal.data.polarized.pullback D.specialProjection

/-- The reduced integral O_E action is also constructed by base change. -/
def action : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) D.abelian :=
  D.integral.universal.data.action.pullback D.specialProjection

/-- Prime-to-q level markings are transported on all test schemes. -/
def level : D.abelian.FullLevel N :=
  D.integral.universal.data.polarized.level.pullback D.specialProjection

/-- Actual finite flat kernels are reduced by pulling back their embedding.
The result is not required to be reduced or etale. -/
def specializeSubgroup {H : Over D.integral.toOver.left}
    (i : H ⟶ D.integral.universal.data.polarized.abelian.scheme) :
    (Over.pullback D.specialProjection).obj H ⟶ D.abelian.scheme :=
  (Over.pullback D.specialProjection).map i

theorem specializeSubgroup_finiteLocallyFree
    (H : Over D.integral.toOver.left)
    [IsFinite H.hom] [Flat H.hom] [LocallyOfFinitePresentation H.hom] :
    IsFinite ((Over.pullback D.specialProjection).obj H).hom ∧
      Flat ((Over.pullback D.specialProjection).obj H).hom ∧
      LocallyOfFinitePresentation ((Over.pullback D.specialProjection).obj H).hom := by
  change IsFinite (pullback.snd H.hom D.specialProjection) ∧
    Flat (pullback.snd H.hom D.specialProjection) ∧
    LocallyOfFinitePresentation (pullback.snd H.hom D.specialProjection)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem specializeSubgroup_closed
    {H : Over D.integral.toOver.left}
    (i : H ⟶ D.integral.universal.data.polarized.abelian.scheme)
    [IsClosedImmersion i.left] : IsClosedImmersion (D.specializeSubgroup i).left := by
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (PELModuli.IntegralModel.Specialization.base_change_square D.specialProjection i) inferInstance

/-- The generic fiber of the integral PEL model retains IntegralModel's actual
identification with the characteristic-zero moduli scheme. -/
def genericComparison :
    (Over.pullback B.generic).obj D.integral.toOver ≅
      (Over.pullback B.fieldExtension).obj (PELModuli.IntegralModel.Reduction.reduction M) :=
  D.integral.genericIso

/-- The quotient-sheaf construction commutes with specialization of the
integral family, with no invertibility assumption on the kernel order. -/
def specializeQuotient
    {R A : Over D.integral.toOver.left} (r₁ r₂ : R ⟶ A) :=
  BaseChange.Construction.relationQuotientSpecialization D.specialProjection r₁ r₂

end SplitPELReduction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Integral.Construction
