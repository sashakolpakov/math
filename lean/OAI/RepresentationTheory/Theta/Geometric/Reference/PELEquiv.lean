import OAI.RepresentationTheory.Theta.Geometric.PELIsometryChern
import OAI.RepresentationTheory.Theta.Geometric.Rational.CMLinearity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceIntrinsic.MarkedAction
import OAI.NumberTheory.ArithmeticGroups.Trace

/-! # PEL Equiv -/

namespace OAI.RepresentationTheory.Theta.Geometric.Reference.PELEquiv

noncomputable section

section

/-! An arbitrary actual reference PEL isomorphism induces a rational
CM-linear isometry of the original Hermitian space. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {s : ℕ} {P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {z w : P.domain}
    {F : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P z} {G : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P w} {hP : P.IsAdmissible}
    {M : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel F hP} {N : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel F hP}
    {M' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel G hP} {N' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel G hP}
    {p : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M N} {p' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M' N'}
    {C : PolarizationConstruction.ReferencePolarizationConstruction p} {C' : PolarizationConstruction.ReferencePolarizationConstruction p'}
    {level : ℕ} [NeZero level] (e : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso (C.pelFamily level) (C'.pelFamily level))

def referencePELPeriodEquiv : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[ℚ] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E :=
  M.nativeReferenceMarking.trans ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLiftIso e.abelian).trans M'.nativeReferenceMarking.symm)

theorem referencePELPeriodEquiv_marking (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    M'.nativeReferenceMarking (referencePELPeriodEquiv e v) =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.abelian.hom (M.nativeReferenceMarking v) :=
  M'.nativeReferenceMarking.apply_symm_apply _

theorem referencePELPeriodEquiv_integral_action (a : NumberField.RingOfIntegers E) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    referencePELPeriodEquiv e ((a : E) • v) = (a : E) • referencePELPeriodEquiv e v := by
  let : IsMonHom (e.abelian.hom : M.abelian.toOver ⟶ M'.abelian.toOver) := e.abelianGroup
  let : IsMonHom (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.functorAction a)) :=
    AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap_isMonHom M.abelian.toOver (M.functorAction a)
  let : IsMonHom (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap M'.abelian.toOver (M'.functorAction a)) :=
    AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap_isMonHom M'.abelian.toOver (M'.functorAction a)
  apply M'.nativeReferenceMarking.injective
  rw [referencePELPeriodEquiv_marking, ← M.nativeReferenceMarking_action]
  have ha : AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.functorAction a) ≫ e.abelian.hom =
      e.abelian.hom ≫ AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap M'.abelian.toOver (M'.functorAction a) := e.equivariant a
  have h := LinearMap.congr_fun (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_congr _ _ ha) (M.nativeReferenceMarking v)
  rw [AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp] at h
  change AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.abelian.hom
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.functorAction a)) (M.nativeReferenceMarking v)) =
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap M'.abelian.toOver (M'.functorAction a))
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.abelian.hom (M.nativeReferenceMarking v)) at h
  exact h.trans ((congrArg (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap M'.abelian.toOver (M'.functorAction a)))
    (referencePELPeriodEquiv_marking e v).symm).trans (M'.nativeReferenceMarking_action a _))

def referencePELFieldEquiv : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E where
  toFun := referencePELPeriodEquiv e
  invFun := (referencePELPeriodEquiv e).symm
  left_inv := (referencePELPeriodEquiv e).symm_apply_apply
  right_inv := (referencePELPeriodEquiv e).apply_symm_apply
  map_add' := (referencePELPeriodEquiv e).map_add
  map_smul' := Rational.CMLinearity.rationalMap_integral_scalar_extension (referencePELPeriodEquiv e).toLinearMap
    (referencePELPeriodEquiv_integral_action e)

theorem referencePELFieldEquiv_trace (x y : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    P.traceForm (referencePELFieldEquiv e x) (referencePELFieldEquiv e y) = P.traceForm x y := by
  have h := PELIsometryChern.pelFamilyIso_chern_isometry C C' e (M.nativeReferenceMarking x) (M.nativeReferenceMarking y)
  rw [← referencePELPeriodEquiv_marking, ← referencePELPeriodEquiv_marking, C'.chern, C.chern] at h
  exact h

theorem referencePELFieldEquiv_hermitian (x y : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b (referencePELFieldEquiv e x) (referencePELFieldEquiv e y) = NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b x y := by
  have hξ : P.imaginaryScalar ≠ 0 := by
    rcases hP with ⟨_, _, _, _, _, _, h, _⟩
    exact h
  have hden : (P.denominator : ℚ) ≠ 0 := by
    rcases hP with ⟨_, _, _, _, _, _, _, _, h, _⟩
    exact_mod_cast h.ne'
  apply (NumberTheory.ArithmeticGroups.Trace.CongruenceLevel.trace_isometries_iff P.b P.imaginaryScalar hξ (referencePELFieldEquiv e)).mp
  intro u v
  exact mul_left_cancel₀ hden (referencePELFieldEquiv_trace e u v)

end

section

/-! The rational map recovered from an actual reference PEL isomorphism
preserves the original integral reference lattice in both directions. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem rationalLiftIso_integral_iff {A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (e : A.toOver ≅ B.toOver) [IsMonHom e.hom] (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom v ∈ AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods B ↔ v ∈ AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods A := by
  constructor
  · intro hv
    have h : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.inv (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom v) ∈ AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods A :=
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift_preserves e.inv _ hv
    exact (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLiftIso e).symm_apply_apply v ▸ h
  · intro hv
    exact AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift_preserves e.hom _ hv

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {s : ℕ} {P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {z w : P.domain}
    {F : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P z} {G : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P w} {hP : P.IsAdmissible}
    {M : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel F hP} {N : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel F hP}
    {M' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel G hP} {N' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel G hP}
    {p : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M N} {p' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M' N'}
    {C : PolarizationConstruction.ReferencePolarizationConstruction p} {C' : PolarizationConstruction.ReferencePolarizationConstruction p'}
    {level : ℕ} [NeZero level] (e : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso (C.pelFamily level) (C'.pelFamily level))

theorem referencePELFieldEquiv_lattice (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    v ∈ P.lattice ↔ referencePELFieldEquiv e v ∈ P.lattice := by
  have he := rationalLiftIso_integral_iff e.abelian (M.nativeReferenceMarking v)
  rw [← referencePELPeriodEquiv_marking, M'.nativeReferenceMarking_integral,
    M.nativeReferenceMarking_integral] at he
  exact he.symm

end

/-! The actual ordered full-level equation forces the recovered rational
CM isometry to be congruent to the identity on the original lattice. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.CategoryTheory.MonObj

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {s : ℕ} {P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {z w : P.domain}
    {F : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P z} {G : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P w} {hP : P.IsAdmissible}
    {M : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel F hP} {N : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel F hP}
    {M' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel G hP} {N' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel G hP}
    {p : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M N} {p' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M' N'}
    {C : PolarizationConstruction.ReferencePolarizationConstruction p} {C' : PolarizationConstruction.ReferencePolarizationConstruction p'}
    {level : ℕ} [NeZero level] (e : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso (C.pelFamily level) (C'.pelFamily level))

theorem referencePELLevel_exp (v : P.lattice) :
    AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M'.abelian.toOver)
        ((level : ℝ)⁻¹ • (M'.nativeReferenceMarking (referencePELFieldEquiv e v.val)).val) =
      AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M'.abelian.toOver)
        ((level : ℝ)⁻¹ • (M'.nativeReferenceMarking v.val).val) := by
  let a := LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase
    (Multiplicative.ofAdd (P.fixedLevelLabel hP level v))
  have he := e.marking (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) a
  change ((M.fixedFullLevel level).hom.app (.op (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) a).val ≫
      e.abelian.hom =
    ((M'.fixedFullLevel level).hom.app (.op (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) a).val at he
  dsimp only [a] at he
  rw [M.fixedFullLevel_native_reference, M'.fixedFullLevel_native_reference] at he
  change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.abelian.hom
      (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) ((level : ℝ)⁻¹ • (M.nativeReferenceMarking v.val).val)) = _ at he
  rw [AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LiftDifferential.IntrinsicLinearMaps.linearLift_exp] at he
  have hl := ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift e.abelian.hom).restrictScalars ℝ).map_smul (level : ℝ)⁻¹
    (M.nativeReferenceMarking v.val).val
  have hm := congrArg Subtype.val (referencePELPeriodEquiv_marking e v.val)
  change (M'.nativeReferenceMarking (referencePELFieldEquiv e v.val)).val =
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift e.abelian.hom (M.nativeReferenceMarking v.val).val at hm
  exact (congrArg (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M'.abelian.toOver))
    (hl.trans (congrArg ((level : ℝ)⁻¹ • ·) hm.symm))).symm.trans he

theorem referencePELFieldEquiv_level (v : P.lattice) :
    ∃ u ∈ P.lattice, referencePELFieldEquiv e v.val - v.val = level • u := by
  let u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E := (level : ℚ)⁻¹ • (referencePELFieldEquiv e v.val - v.val)
  have hu : u ∈ P.lattice := by
    apply (M'.nativeReferenceMarking_integral u).mp
    change (M'.nativeReferenceMarking u).val ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice M'.abelian
    have hvec : (M'.nativeReferenceMarking u).val =
        (level : ℝ)⁻¹ • (M'.nativeReferenceMarking (referencePELFieldEquiv e v.val)).val -
          (level : ℝ)⁻¹ • (M'.nativeReferenceMarking v.val).val := by
      change (M'.nativeReferenceMarking ((level : ℚ)⁻¹ • (referencePELFieldEquiv e v.val - v.val))).val = _
      rw [map_smul, map_sub]
      change (level : ℚ)⁻¹ • ((M'.nativeReferenceMarking (referencePELFieldEquiv e v.val)).val -
        (M'.nativeReferenceMarking v.val).val) = _
      rw [← IsScalarTower.algebraMap_smul ℝ ((level : ℚ)⁻¹), map_inv₀, map_natCast, smul_sub]
    rw [hvec]
    change AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialLocal.Constructions.Exponential.expAddHom (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M'.abelian.toOver) (_ - _) = 0
    rw [map_sub, sub_eq_zero]
    exact congrArg Additive.ofMul (referencePELLevel_exp e v)
  refine ⟨u, hu, ?_⟩
  change referencePELFieldEquiv e v.val - v.val = level • ((level : ℚ)⁻¹ • _)
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne level)), one_smul]

end

end OAI.RepresentationTheory.Theta.Geometric.Reference.PELEquiv
