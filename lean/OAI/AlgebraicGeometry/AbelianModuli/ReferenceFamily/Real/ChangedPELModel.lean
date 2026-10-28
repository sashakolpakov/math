import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.ChangedModel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralPolarizationType
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRank
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodActionLieRanks
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PELMarking
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.OrderedLatticeLevel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.DivisionNaturality
import OAI.RepresentationTheory.Theta.Geometric.LevelLabels
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Objects

/-! # Changed PEL Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.ChangedPELModel.RealChangedPEL

noncomputable section

/-! A real change of the native period lattice, commuting with the
original action and preserving its Chern form, gives an actual PEL
object with the original polarization type and ordered level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.CategoryTheory.MonObj TensorProduct

open OAI.AlgebraicGeometry.Picard.ThetaConstruction.DefinitionsIntegral OAI.RepresentationTheory.Theta.Geometric.LevelLabels
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

attribute [local implicit_reducible] Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.abelianScheme
  Picard.ThetaConstruction.IntegralDualModel.Geometric.IntegralDualAlgebraicModel.abelianScheme Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native
  Picard.ThetaConstruction.ProjectivePeriodData.Geometric.projectivePeriodData RepresentationTheory.Theta.Geometric.Torus.Data.CM.ProjectivePeriodData.ofCompactProjectiveTorus
  Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.toOver

theorem extendAction_intertwines
    {E V W : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (ρ : NumberField.RingOfIntegers E →+* Module.End ℚ V)
    (σ : NumberField.RingOfIntegers E →+* Module.End ℚ W) (f : V →ₗ[ℚ] W)
    (h : ∀ a x, f (ρ a x) = σ a (f x)) (a : E) (x : V) :
    f (Integral.ActionExtension.extendIntegralAction ρ a x) = Integral.ActionExtension.extendIntegralAction σ a (f x) := by
  obtain ⟨t, rfl⟩ := (Integral.ActionExtension.integralRationalTensorIso (E := E)).surjective a
  induction t using TensorProduct.inductionOn with
  | add t u ht hu => simp only [map_add, LinearMap.add_apply, ht, hu]
  | tmul q a =>
    rw [Integral.ActionExtension.extendIntegralAction_tmul, Integral.ActionExtension.extendIntegralAction_tmul]
    change f (q • ρ a x) = q • σ a (f x)
    rw [f.map_smul, h]

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K]
    {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {κ : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (.of K)}
    (A : PEL.Objects.PELObject P iota N (Over.mk κ))

local notation "PA" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized
local notation "A₀" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.polarized.abelian PA

variable (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (Picard.ThetaConstruction.DefinitionsIntegral.Index (3 * s))
      (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized)))
    (u : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel
      (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized)) ≃ₗ[ℝ]
      HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel
        (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized)))
    (R : ChangedModel.RealChangedAlgebraicModel
      (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized))
      b u (Intrinsic.ChernPairing.polarizationLineBundle A.polarized)
      (Intrinsic.ChernPairing.polarizationLineBundle_ample A.polarized))
    (hcomm : ∀ a x, u (Intrinsic.IntegralAction.IntrinsicIntegralAction.linearAction A.polarized.abelian
      (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized) A.action a x) =
      Intrinsic.IntegralAction.IntrinsicIntegralAction.linearAction A.polarized.abelian
        (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized) A.action a (u x))

local instance : IsIntegral (A₀).toOver.left := (A₀).variety.property
local instance : Smooth (A₀).toOver.hom := (A₀).variety.presentation.smooth
local instance : IsIntegral A.polarized.abelian.scheme.left := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral A.polarized.abelian
local instance : IsIntegral R.model.abelian.toOver.left := R.model.abelian.variety.property
local instance : Smooth R.model.abelian.toOver.hom := R.model.abelian.variety.presentation.smooth
local instance : IsIntegral R.model.abelianScheme.scheme.left := R.model.abelian.variety.property

def torusAction : NumberField.RingOfIntegers E →+* Module.End ℂ (Picard.ThetaConstruction.DefinitionsIntegral.Tangent (3 * s)) :=
  R.coordinates.conjRingEquiv.toRingHom.comp
    (Intrinsic.IntegralAction.IntrinsicIntegralAction.linearAction A.polarized.abelian PA A.action)

theorem torusAction_apply (a : NumberField.RingOfIntegers E) (v : Picard.ThetaConstruction.DefinitionsIntegral.Tangent (3 * s)) :
    torusAction A b u R a v = R.coordinates
      (Intrinsic.IntegralAction.IntrinsicIntegralAction.linearAction A.polarized.abelian PA A.action a (R.coordinates.symm v)) := rfl

include hcomm in
theorem torusAction_preserves (a : NumberField.RingOfIntegers E) (v : Picard.ThetaConstruction.DefinitionsIntegral.Tangent (3 * s))
    (hv : v ∈ R.torus.lattice) : torusAction A b u R a v ∈ R.torus.lattice := by
  apply (R.lattice _).mpr
  rw [torusAction_apply, R.coordinates.symm_apply_apply, hcomm]
  exact Intrinsic.IntegralAction.IntrinsicIntegralAction.linearAction_preserves A.polarized.abelian PA A.action a _
    ((R.lattice v).mp hv)

theorem torusAction_adjoint (a : NumberField.RingOfIntegers E) (v w : Picard.ThetaConstruction.DefinitionsIntegral.Tangent (3 * s)) :
    R.torus.riemannForm
      (torusAction A b u R (NumberField.IsCMField.ringOfIntegersComplexConj E a) v) w =
        R.torus.riemannForm v (torusAction A b u R a w) := by
  obtain ⟨v, rfl⟩ := R.coordinates.surjective v
  obtain ⟨w, rfl⟩ := R.coordinates.surjective w
  rw [torusAction_apply, torusAction_apply,
    R.coordinates.symm_apply_apply, R.coordinates.symm_apply_apply, R.form, R.form]
  exact ActionData.RosatiConjugation.native_riemann_adjoint A.polarized A.action A.rosati a v w

def action : ActionData.IntegralAction (NumberField.RingOfIntegers E) R.model.abelianScheme :=
  ThetaConstructionIntegralAction.integralAction R.model (torusAction A b u R)
    (torusAction_preserves A b u R hcomm)

theorem action_lift (a : NumberField.RingOfIntegers E)
    (v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A₀) :
    Intrinsic.Maps.IntrinsicLinearMaps.linearLift ((RealChangedPEL.action A b u R hcomm).map a) (R.tangentEquiv v) =
      R.tangentEquiv (Intrinsic.IntegralAction.IntrinsicIntegralAction.linearAction A.polarized.abelian PA A.action a v) := by
  change Intrinsic.Maps.IntrinsicLinearMaps.linearLift ((RealChangedPEL.action A b u R hcomm).map a)
    (R.model.periodDifferential (R.coordinates v)) = _
  unfold RealChangedPEL.action
  rw [ThetaConstructionIntegralAction.integralAction_lift_apply, torusAction_apply,
    R.coordinates.symm_apply_apply]
  rfl

theorem action_realPeriodEquiv (a : NumberField.RingOfIntegers E)
    (v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A₀) :
    Intrinsic.Maps.IntrinsicLinearMaps.linearLift ((RealChangedPEL.action A b u R hcomm).map a) (R.realPeriodEquiv v) =
      R.realPeriodEquiv (Intrinsic.IntegralAction.IntrinsicIntegralAction.linearAction A.polarized.abelian PA A.action a v) := by
  have hu : Intrinsic.IntegralAction.IntrinsicIntegralAction.linearAction A.polarized.abelian PA A.action a (u.symm v) =
      u.symm (Intrinsic.IntegralAction.IntrinsicIntegralAction.linearAction A.polarized.abelian PA A.action a v) := by
    apply u.injective
    rw [hcomm, u.apply_symm_apply, u.apply_symm_apply]
  change Intrinsic.Maps.IntrinsicLinearMaps.linearLift ((RealChangedPEL.action A b u R hcomm).map a) (R.tangentEquiv (u.symm v)) =
    R.tangentEquiv (u.symm (Intrinsic.IntegralAction.IntrinsicIntegralAction.linearAction A.polarized.abelian PA A.action a v))
  rw [action_lift, hu]

theorem rationalMarking_action (a : NumberField.RingOfIntegers E) (x : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A₀) :
    Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift ((RealChangedPEL.action A b u R hcomm).map a) (R.rationalMarking x) =
      R.rationalMarking (Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.rationalAction A.polarized.abelian PA A.action a x) := by
  apply Subtype.ext
  exact action_realPeriodEquiv A b u R hcomm a x.val

local notation "PM" => R.model.abelian.variety.presentation.projective

theorem nativeRationalMarking_action (a : NumberField.RingOfIntegers E) (x : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A₀) :
    Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.rationalAction R.model.abelianScheme PM (RealChangedPEL.action A b u R hcomm) a
      (R.rationalMarking x) =
        R.rationalMarking (Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.rationalAction A.polarized.abelian PA A.action a x) := by
  have hm := PeriodActionLieRanks.IntrinsicIntegralAction.nativeMap_eq_original R.model.abelianScheme PM
    (RealChangedPEL.action A b u R hcomm) a
  have hl := Intrinsic.Maps.IntrinsicLinearMaps.linearLift_congr _ _ hm
  have he : Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.rationalAction R.model.abelianScheme PM (RealChangedPEL.action A b u R hcomm) a
      (R.rationalMarking x) = Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift ((RealChangedPEL.action A b u R hcomm).map a) (R.rationalMarking x) := by
    apply Subtype.ext
    exact LinearMap.congr_fun hl (R.rationalMarking x).val
  exact he.trans (rationalMarking_action A b u R hcomm a x)

def fieldPeriodEquiv :
    let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.polarized.abelian PA A.action
    let : Module E (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods R.model.abelian) :=
      Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule R.model.abelianScheme PM (RealChangedPEL.action A b u R hcomm)
    Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A₀ ≃ₗ[E] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods R.model.abelian := by
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.polarized.abelian PA A.action
  let : Module E (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods R.model.abelian) :=
    Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule R.model.abelianScheme PM (RealChangedPEL.action A b u R hcomm)
  refine { R.rationalMarking.toEquiv with
    map_add' := R.rationalMarking.map_add
    map_smul' := ?_ }
  intro a x
  change R.rationalMarking (Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction A.polarized.abelian PA A.action a x) =
    Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction R.model.abelianScheme PM (RealChangedPEL.action A b u R hcomm) a
      (R.rationalMarking x)
  exact extendAction_intertwines _ _ R.rationalMarking.toLinearMap
    (fun a x => (nativeRationalMarking_action A b u R hcomm a x).symm) a x

theorem action_derivative (a : NumberField.RingOfIntegers E)
    (v : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A₀) :
    RepresentationTheory.Theta.Geometric.GroupDerivative.nativeGroupDerivative ((RealChangedPEL.action A b u R hcomm).map a) (R.tangentEquiv v) =
      R.tangentEquiv (RepresentationTheory.Theta.Geometric.GroupDerivative.nativeGroupDerivative (A.action.map a) v) := by
  calc
    RepresentationTheory.Theta.Geometric.GroupDerivative.nativeGroupDerivative ((RealChangedPEL.action A b u R hcomm).map a) (R.tangentEquiv v) =
        Intrinsic.Maps.IntrinsicLinearMaps.linearLift ((RealChangedPEL.action A b u R hcomm).map a) (R.tangentEquiv v) :=
      (LinearMap.congr_fun (Intrinsic.LiftDifferential.IntrinsicLinearMaps.linearLift_eq_nativeDifferential
        ((RealChangedPEL.action A b u R hcomm).map a)) (R.tangentEquiv v)).symm
    _ = R.tangentEquiv (Intrinsic.IntegralAction.IntrinsicIntegralAction.linearAction A.polarized.abelian PA A.action a v) :=
      action_lift A b u R hcomm a v
    _ = R.tangentEquiv (RepresentationTheory.Theta.Geometric.GroupDerivative.nativeGroupDerivative (A.action.map a) v) :=
      congrArg R.tangentEquiv (LinearMap.congr_fun
        (PeriodActionLieRanks.IntrinsicIntegralAction.linearAction_eq_nativeLieDifferential A.polarized.abelian PA A.action a) v)

theorem action_lieRanks :
    PEL.Objects.HasPrescribedLieRanks P iota (Over.mk κ) R.model.abelianScheme (RealChangedPEL.action A b u R hcomm) := by
  intro F _ _ j p hp τ
  exact LieRank.LieRankLinearTransport.hasLieRank_after_baseChange
    A.polarized.abelian A.action R.model.abelianScheme (RealChangedPEL.action A b u R hcomm)
    R.tangentEquiv (action_derivative A b u R hcomm) F p _ _ (A.lieRanks F j p hp τ)

def modelDivisionEquiv [NeZero N] :
    (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice R.model.abelian ⧸ LatticeDivision.TorusTorsion.multipleSubgroup (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice R.model.abelian) N) ≃+
      Additive (R.model.abelianScheme.torsionPoints N (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) :=
  (LatticeDivision.TorusTorsion.latticeDivisionEquiv (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice R.model.abelian) N).trans
    ((TorsionCongruence.TorusTorsion.killedByEquiv (Intrinsic.Maps.IntrinsicAlgebraicMaps.periodAddEquiv R.model.abelian) N).trans
      (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.torsionAddEquiv R.model.abelianScheme N).symm)

def orderedLatticeLabels [NeZero N] :
    (Fin (2 * (3 * s)) → ZMod N) ≃+
      (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice R.model.abelian ⧸ LatticeDivision.TorusTorsion.multipleSubgroup (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice R.model.abelian) N) :=
  (Intrinsic.OrderedLatticeLevel.nativeOrderedLatticeLevel A.polarized.abelian PA A.polarized.level).trans
    (LatticeDivision.TorusTorsion.modNEquiv N R.latticeEquiv.toAddEquiv)

def torsionLabels [NeZero N] :
    Multiplicative (Fin (2 * (3 * s)) → ZMod N) ≃*
      R.model.abelianScheme.torsionPoints N (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase) :=
  ((orderedLatticeLabels A b u R).trans (modelDivisionEquiv A b u R)).toMultiplicativeLeft

def fullLevel [NeZero N] : R.model.abelianScheme.FullLevel N :=
  RepresentationTheory.Theta.Geometric.LevelLabels.relabelFullLevel R.model.abelianScheme
    (ReferenceFamily.Complex.ComplexLevel.fullLevel R.model.abelianScheme
      R.model.abelian.variety.presentation.projective N) (torsionLabels A b u R)

theorem fullLevel_points [NeZero N] :
    RepresentationTheory.Theta.Geometric.LevelLabels.fullLevelPointEquiv R.model.abelianScheme (fullLevel A b u R) = torsionLabels A b u R :=
  RepresentationTheory.Theta.Geometric.LevelLabels.relabelFullLevel_points R.model.abelianScheme _ _

def originalLevelLabel [NeZero N] (l : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A₀) :
    Multiplicative (Fin (2 * (3 * s)) → ZMod N) :=
  Multiplicative.ofAdd ((Intrinsic.OrderedLatticeLevel.nativeOrderedLatticeLevel A.polarized.abelian PA A.polarized.level).symm
    (QuotientAddGroup.mk l))

theorem originalLevelLabel_surjective [NeZero N] : Function.Surjective (originalLevelLabel A) := by
  intro c
  obtain ⟨l, hl⟩ := QuotientAddGroup.mk_surjective
    (Intrinsic.OrderedLatticeLevel.nativeOrderedLatticeLevel A.polarized.abelian PA A.polarized.level c.toAdd)
  refine ⟨l, ?_⟩
  simp only [originalLevelLabel, hl, AddEquiv.symm_apply_apply]
  exact ofAdd_toAdd c

theorem originalLevelLabel_congruent [NeZero N] (l m : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A₀)
    (h : ∃ k : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A₀, m - l = N • k) :
    originalLevelLabel A m = originalLevelLabel A l := by
  apply congrArg (fun x => Multiplicative.ofAdd
    ((Intrinsic.OrderedLatticeLevel.nativeOrderedLatticeLevel A.polarized.abelian PA A.polarized.level).symm x))
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  obtain ⟨k, hk⟩ := h
  exact ⟨k, hk.symm⟩

theorem originalLevelLabel_point [NeZero N] (l : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A₀) :
    (A.polarized.level.hom.app (.op (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase))
      (LocallyConstant.const Foundations.Scheme.ProjectiveSpace.complexBase (originalLevelLabel A l))).val =
      HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A₀).toOver) ((N : ℝ)⁻¹ • l.val) ≫
        (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A.polarized.abelian PA).hom := by
  have h := Intrinsic.OrderedLatticeLevel.nativeDivisionEquiv_ordered A.polarized.abelian PA A.polarized.level
    ((Intrinsic.OrderedLatticeLevel.nativeOrderedLatticeLevel A.polarized.abelian PA A.polarized.level).symm
      (QuotientAddGroup.mk l))
  rw [AddEquiv.apply_symm_apply] at h
  have he := congrArg (fun x : Additive (A.polarized.abelian.torsionPoints N
    (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) => x.toMul.val) h
  rw [Intrinsic.DivisionNaturality.nativeDivisionEquiv_mk] at he
  change HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A₀).toOver) ((N : ℚ)⁻¹ • l.val) ≫
    (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A.polarized.abelian PA).hom = _ at he
  refine he.symm.trans ?_
  have hs : (N : ℚ)⁻¹ • l.val = (N : ℝ)⁻¹ • l.val := by
    simpa only [map_inv₀, map_natCast] using
      (IsScalarTower.algebraMap_smul ℝ ((N : ℚ)⁻¹) l.val).symm
  rw [hs]

theorem fullLevel_originalLabel [NeZero N] (l : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A₀) :
    (RepresentationTheory.Theta.Geometric.LevelLabels.fullLevelPointEquiv R.model.abelianScheme (fullLevel A b u R) (originalLevelLabel A l)).val =
      HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints R.model.abelian.toOver)
        ((N : ℝ)⁻¹ • R.realPeriodEquiv l.val) := by
  rw [fullLevel_points]
  change (modelDivisionEquiv A b u R (LatticeDivision.TorusTorsion.modNEquiv N R.latticeEquiv.toAddEquiv
    (Intrinsic.OrderedLatticeLevel.nativeOrderedLatticeLevel A.polarized.abelian PA A.polarized.level
      ((Intrinsic.OrderedLatticeLevel.nativeOrderedLatticeLevel A.polarized.abelian PA A.polarized.level).symm
        (QuotientAddGroup.mk l))))).toMul.val = _
  rw [AddEquiv.apply_symm_apply, LatticeDivision.TorusTorsion.modNEquiv_mk]
  change HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints R.model.abelian.toOver)
    ((N : ℚ)⁻¹ • R.realPeriodEquiv l.val) = _
  apply congrArg (HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints R.model.abelian.toOver))
  simpa only [map_inv₀, map_natCast] using
    (IsScalarTower.algebraMap_smul ℝ ((N : ℚ)⁻¹) (R.realPeriodEquiv l.val)).symm

variable {D : Picard.ThetaConstruction.IntegralDualModel.Geometric.IntegralDualAlgebraicModel R.torus} {p : Picard.ThetaConstruction.IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny R.model D}
    (C : Picard.ThetaConstruction.PrimitiveDual.Geometric.PrimitiveDualConstruction p) (hP : P.IsAdmissible)

theorem rationalMarking_chern
    (hu : ∀ x y, (Intrinsic.RiemannForm.nativeRiemannForm A₀ (Intrinsic.ChernPairing.polarizationLineBundle A.polarized)
      (Intrinsic.ChernPairing.polarizationLineBundle_ample A.polarized) (u x) (u y)).im =
      (Intrinsic.RiemannForm.nativeRiemannForm A₀ (Intrinsic.ChernPairing.polarizationLineBundle A.polarized)
        (Intrinsic.ChernPairing.polarizationLineBundle_ample A.polarized) x y).im)
    (x y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A₀) :
    Intrinsic.ChernPairing.nativeChernForm R.model.abelian C.ampleLine (R.rationalMarking x) (R.rationalMarking y) =
      Intrinsic.ChernPairing.nativePolarizationForm A.polarized x y := by
  apply Rat.cast_injective (α := ℝ)
  have hchange := hu (u.symm x.val) (u.symm y.val)
  rw [u.apply_symm_apply, u.apply_symm_apply] at hchange
  calc
    (Intrinsic.ChernPairing.nativeChernForm R.model.abelian C.ampleLine (R.rationalMarking x) (R.rationalMarking y) : ℝ) =
        (Intrinsic.RiemannForm.nativeRiemannForm R.model.abelian C.ampleLine C.ample
          (R.rationalMarking x).val (R.rationalMarking y).val).im :=
      (Intrinsic.RiemannForm.nativeRiemannForm_period R.model.abelian C.ampleLine C.ample _ _).symm
    _ = (R.torus.riemannForm (R.coordinates (u.symm x.val)) (R.coordinates (u.symm y.val))).im :=
      congrArg Complex.im (ThetaConstructionIntegralAction.primitive_riemann R.model C _ _)
    _ = (Intrinsic.RiemannForm.nativeRiemannForm A₀ (Intrinsic.ChernPairing.polarizationLineBundle A.polarized)
        (Intrinsic.ChernPairing.polarizationLineBundle_ample A.polarized) (u.symm x.val) (u.symm y.val)).im :=
      congrArg Complex.im (R.form _ _)
    _ = (Intrinsic.RiemannForm.nativeRiemannForm A₀ (Intrinsic.ChernPairing.polarizationLineBundle A.polarized)
        (Intrinsic.ChernPairing.polarizationLineBundle_ample A.polarized) x.val y.val).im := hchange.symm
    _ = (Intrinsic.ChernPairing.nativePolarizationForm A.polarized x y : ℝ) :=
      Intrinsic.RiemannForm.nativeRiemannForm_period A₀ (Intrinsic.ChernPairing.polarizationLineBundle A.polarized)
        (Intrinsic.ChernPairing.polarizationLineBundle_ample A.polarized) x y

def polarizationType : Picard.ThetaConstruction.PolarizationTypeData.Geometric.IntegralPolarizationType (Intrinsic.ChernIntegralPeriods.nativeIntegralChernMatrix A₀
    (Intrinsic.ChernPairing.polarizationLineBundle A.polarized) b) :=
  Intrinsic.IntegralPolarizationType.nativeIntegralPolarizationType A.polarized b hP.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

def object [NeZero N] : PEL.Objects.PELObject P iota N (Over.mk κ) where
  polarized := C.polarized (polarizationType A b hP) (fullLevel A b u R)
  action := RealChangedPEL.action A b u R hcomm
  rosati := ThetaConstructionIntegralAction.primitive_rosati R.model C
    (torusAction A b u R) (torusAction_preserves A b u R hcomm)
    (torusAction_adjoint A b u R) (polarizationType A b hP) (fullLevel A b u R)
  lieRanks := action_lieRanks A b u R hcomm

@[simp] theorem object_abelian [NeZero N] :
    (object A b u R hcomm C hP).polarized.abelian = R.model.abelianScheme := rfl

def objectFieldMarking [NeZero N] (hs : 0 < s)
    (hdegree : Module.finrank ℚ E = 2 * s) :
    let : Module E (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods R.model.abelian) :=
      Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule (object A b u R hcomm C hP).polarized.abelian PM
        (object A b u R hcomm C hP).action
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods R.model.abelian := by
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.polarized.abelian PA A.action
  let : Module E (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods R.model.abelian) :=
    Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule (object A b u R hcomm C hP).polarized.abelian PM
      (object A b u R hcomm C hP).action
  exact (Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A.polarized.abelian PA A.action s hs rfl hdegree).symm.trans
    (fieldPeriodEquiv A b u R hcomm)

theorem object_level_of_period [NeZero N] (l : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A₀)
    (v : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods R.model.abelian)
    (hv : v = R.rationalMarking (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A₀) l)) :
    ((object A b u R hcomm C hP).polarized.level.hom.app (.op (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase))
      (LocallyConstant.const Foundations.Scheme.ProjectiveSpace.complexBase (originalLevelLabel A l))).val =
        HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints R.model.abelian.toOver) ((N : ℝ)⁻¹ • v.val) := by
  subst v
  exact fullLevel_originalLabel A b u R l

theorem object_rationalMarking_polarization [NeZero N]
    (hu : ∀ x y, (Intrinsic.RiemannForm.nativeRiemannForm A₀ (Intrinsic.ChernPairing.polarizationLineBundle A.polarized)
      (Intrinsic.ChernPairing.polarizationLineBundle_ample A.polarized) (u x) (u y)).im =
      (Intrinsic.RiemannForm.nativeRiemannForm A₀ (Intrinsic.ChernPairing.polarizationLineBundle A.polarized)
        (Intrinsic.ChernPairing.polarizationLineBundle_ample A.polarized) x y).im)
    (x y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A₀) :
    Intrinsic.ChernPairing.nativePolarizationForm (object A b u R hcomm C hP).polarized
        (R.rationalMarking x) (R.rationalMarking y) = Intrinsic.ChernPairing.nativePolarizationForm A.polarized x y := by
  have h := ThetaConstructionIntegralAction.primitive_chern_eq_polarization R.model C
    (polarizationType A b hP) (fullLevel A b u R)
  exact (LinearMap.congr_fun (LinearMap.congr_fun h (R.rationalMarking x))
    (R.rationalMarking y)).symm.trans (rationalMarking_chern A b u R C hu x y)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.ChangedPELModel.RealChangedPEL
