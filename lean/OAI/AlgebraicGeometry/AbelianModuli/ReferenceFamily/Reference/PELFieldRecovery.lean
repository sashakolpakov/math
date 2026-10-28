import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardPolarizationComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PELObject
import OAI.RepresentationTheory.Theta.Geometric.Rational.CMLinearity
import OAI.NumberTheory.ArithmeticGroups.Trace
import Mathlib.Algebra.Module.Rat

/-! # PEL Field Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PELFieldRecovery.ReferencePicardConstruction

noncomputable section

/-! An actual reference PEL isomorphism recovers an E-linear isometry
of the original rational Hermitian space through its native periods. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.NumberTheory.ArithmeticGroups.Trace.CongruenceLevel OAI.RepresentationTheory.Theta.Geometric.Rational.CMLinearity

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E] [Field K]
    {s : ℕ} {P : Datum.RankThreePELDatum E s} {z w : P.domain}
    {F : Fiber.ReferenceAnalyticFiber P z} {G : Fiber.ReferenceAnalyticFiber P w} {hP : P.IsAdmissible}
    {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {D : DualModel.ReferenceDualModel F hP}
    {W : AlgebraicModel.ReferenceAlgebraicModel G hP} {D' : DualModel.ReferenceDualModel G hP}
    {p : IsogenyKernel.ReferenceLatticeIsogeny M D} {q : IsogenyKernel.ReferenceLatticeIsogeny W D'}
    (C : PicardConstruction.ReferencePicardConstruction p) (C' : PicardConstruction.ReferencePicardConstruction q)
    (iota : E →+* K) (κ : K →+* ℂ) (he : κ.comp iota = P.μ) (N : ℕ) [NeZero N]
    (e : PEL.Objects.PELIso (C.pelObject iota κ he N) (C'.pelObject iota κ he N))

local instance : IsMonHom (show M.abelian.toOver ⟶ W.abelian.toOver from e.polarized.abelian.hom) :=
  e.polarized.abelianGroup
local instance : IsMonHom (show D.abelian.toOver ⟶ D'.abelian.toOver from e.polarized.dual.hom) :=
  e.polarized.dualGroup

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction.ReferencePicardConstruction.referencePELIso_periodPairing (x : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods D.abelian) (y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) :
    C'.referencePeriodPairing (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.polarized.dual.hom x) (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.polarized.abelian.hom y) =
      C.referencePeriodPairing x y := by
  have h := RepresentationTheory.Theta.Geometric.LinePeriodPairing.linePeriodPairing_pullback D.abelian M.abelian D'.abelian W.abelian
    e.polarized.dual.hom e.polarized.abelian.hom (HilbertConstruction.Line.Bundles.LineBundle.classOf C'.poincare) x y
  exact h.symm.trans (congrArg (fun Q => RepresentationTheory.Theta.Geometric.LinePeriodPairing.linePeriodPairing D.abelian M.abelian Q x y) e.polarized.poincare)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction.ReferencePicardConstruction.referencePELIso_chern (x y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) :
    Intrinsic.ChernPairing.nativeChernForm W.abelian C'.ampleLine (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.polarized.abelian.hom x)
      (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.polarized.abelian.hom y) = Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine x y := by
  let f : M.abelian.toOver ⟶ W.abelian.toOver := e.polarized.abelian.hom
  let d : D.abelian.toOver ⟶ D'.abelian.toOver := e.polarized.dual.hom
  let a : M.abelian.toOver ⟶ D.abelian.toOver := p.isogeny.hom
  let b : W.abelian.toOver ⟶ D'.abelian.toOver := q.isogeny.hom
  let : IsMonHom f := e.polarized.abelianGroup
  let : IsMonHom d := e.polarized.dualGroup
  let : IsMonHom a := p.isogeny.preservesGroup
  let : IsMonHom b := q.isogeny.preservesGroup
  have hp : a ≫ d = f ≫ b := e.polarized.polarization
  have h := LinearMap.congr_fun (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_congr _ _ hp) x
  rw [Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp] at h
  change Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.polarized.dual.hom (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift p.isogeny.hom x) =
    Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift q.isogeny.hom (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.polarized.abelian.hom x) at h
  rw [← C'.referencePeriodPairing_isogeny, ← h, C.referencePELIso_periodPairing C' iota κ he N e,
    C.referencePeriodPairing_isogeny]

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction.ReferencePicardConstruction.referencePeriodIso : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[ℚ] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E :=
  M.nativeReferenceMarking.trans ((Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLiftIso
    (show M.abelian.toOver ≅ W.abelian.toOver from e.polarized.abelian)).trans W.nativeReferenceMarking.symm)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction.ReferencePicardConstruction.referencePeriodIso_marking (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    W.nativeReferenceMarking (C.referencePeriodIso C' iota κ he N e v) =
      Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.polarized.abelian.hom (M.nativeReferenceMarking v) :=
  W.nativeReferenceMarking.apply_symm_apply _

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction.ReferencePicardConstruction.referencePeriodIso_integral_action (a : NumberField.RingOfIntegers E) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    C.referencePeriodIso C' iota κ he N e ((a : E) • v) = (a : E) • C.referencePeriodIso C' iota κ he N e v := by
  apply W.nativeReferenceMarking.injective
  rw [C.referencePeriodIso_marking, ← M.nativeReferenceMarking_action]
  let f : M.abelian.toOver ⟶ W.abelian.toOver := e.polarized.abelian.hom
  let aM : M.abelian.toOver ⟶ M.abelian.toOver := AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.functorAction a)
  let aW : W.abelian.toOver ⟶ W.abelian.toOver := AbelianScheme.TateComparison.End.endSchemeMap W.abelian.toOver (W.functorAction a)
  let : IsMonHom f := e.polarized.abelianGroup
  let : IsMonHom aM := AbelianScheme.TateComparison.End.endSchemeMap_isMonHom M.abelian.toOver (M.functorAction a)
  let : IsMonHom aW := AbelianScheme.TateComparison.End.endSchemeMap_isMonHom W.abelian.toOver (W.functorAction a)
  have ha : aM ≫ f = f ≫ aW := e.action a
  have h := LinearMap.congr_fun (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_congr _ _ ha) (M.nativeReferenceMarking v)
  rw [Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp] at h
  change Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.polarized.abelian.hom
    (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.functorAction a)) (M.nativeReferenceMarking v)) =
    Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (AbelianScheme.TateComparison.End.endSchemeMap W.abelian.toOver (W.functorAction a))
      (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.polarized.abelian.hom (M.nativeReferenceMarking v)) at h
  exact h.trans ((congrArg (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (AbelianScheme.TateComparison.End.endSchemeMap W.abelian.toOver (W.functorAction a)))
    (C.referencePeriodIso_marking C' iota κ he N e v).symm).trans (W.nativeReferenceMarking_action a _))

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction.ReferencePicardConstruction.referenceFieldIso : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E where
  toFun := C.referencePeriodIso C' iota κ he N e
  invFun := (C.referencePeriodIso C' iota κ he N e).symm
  left_inv := (C.referencePeriodIso C' iota κ he N e).symm_apply_apply
  right_inv := (C.referencePeriodIso C' iota κ he N e).apply_symm_apply
  map_add' := (C.referencePeriodIso C' iota κ he N e).map_add
  map_smul' := @RepresentationTheory.Theta.Geometric.Rational.CMLinearity.rationalMap_integral_scalar_extension E (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) _ _ _ _ _
    (@IsScalarTower.rat E (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) _ _ _ (@Algebra.toModule ℚ E _ _ DivisionRing.toRatAlgebra) _)
    _ _ _ (@IsScalarTower.rat E (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) _ _ _ (@Algebra.toModule ℚ E _ _ DivisionRing.toRatAlgebra) _)
    (C.referencePeriodIso C' iota κ he N e).toLinearMap
    (C.referencePeriodIso_integral_action C' iota κ he N e)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction.ReferencePicardConstruction.referenceFieldIso_marking (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    W.nativeReferenceMarking (C.referenceFieldIso C' iota κ he N e v) =
      Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.polarized.abelian.hom (M.nativeReferenceMarking v) :=
  C.referencePeriodIso_marking C' iota κ he N e v

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction.ReferencePicardConstruction.referenceFieldIso_trace (x y : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    P.traceForm (C.referenceFieldIso C' iota κ he N e x) (C.referenceFieldIso C' iota κ he N e y) = P.traceForm x y := by
  have h := C.referencePELIso_chern C' iota κ he N e (M.nativeReferenceMarking x) (M.nativeReferenceMarking y)
  rw [← C.referenceFieldIso_marking, ← C.referenceFieldIso_marking, C'.chern, C.chern] at h
  exact h

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction.ReferencePicardConstruction.referenceFieldIso_unitary :
    C.referenceFieldIso C' iota κ he N e ∈ Groups.unitarySubgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b) := by
  have hξ : P.imaginaryScalar ≠ 0 := hP.2.2.2.2.2.2.1
  have hden : (P.denominator : ℚ) ≠ 0 := by
    have hd : 0 < P.denominator := hP.2.2.2.2.2.2.2.2.1
    exact_mod_cast hd.ne'
  apply (NumberTheory.ArithmeticGroups.Trace.CongruenceLevel.trace_isometries_iff P.b P.imaginaryScalar hξ (C.referenceFieldIso C' iota κ he N e)).mp
  intro u v
  exact mul_left_cancel₀ hden (C.referenceFieldIso_trace C' iota κ he N e u v)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PELFieldRecovery.ReferencePicardConstruction
