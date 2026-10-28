import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PELFieldRecovery
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DeterminantCongruence
import OAI.RepresentationTheory.Theta.Geometric.LatticeDeterminantCongruence

/-! # PEL Arithmetic Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PELArithmeticRecovery

noncomputable section

/-! Actual reference PEL isomorphisms recover integral principal
special unitary maps on the prescribed rational E-space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.CategoryTheory.MonObj

theorem nativeRationalIso_integral_iff {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (e : A.toOver ≅ B.toOver)
    [IsMonHom e.hom] (v : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom v ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods B ↔ v ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods A := by
  constructor
  · intro hv
    have h : Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.inv (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom v) ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods A := Intrinsic.Maps.IntrinsicLinearMaps.linearLift_preserves e.inv _ hv
    exact (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLiftIso e).symm_apply_apply v ▸ h
  · exact fun hv => Intrinsic.Maps.IntrinsicLinearMaps.linearLift_preserves e.hom _ hv

namespace ReferencePicardConstruction

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E] [Field K]
    {s : ℕ} {P : Datum.RankThreePELDatum E s} {z w : P.domain}
    {F : Fiber.ReferenceAnalyticFiber P z} {G : Fiber.ReferenceAnalyticFiber P w} {hP : P.IsAdmissible}
    {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {D : DualModel.ReferenceDualModel F hP}
    {W : AlgebraicModel.ReferenceAlgebraicModel G hP} {D' : DualModel.ReferenceDualModel G hP}
    {p : IsogenyKernel.ReferenceLatticeIsogeny M D} {q : IsogenyKernel.ReferenceLatticeIsogeny W D'}
    (C : PicardConstruction.ReferencePicardConstruction p) (C' : PicardConstruction.ReferencePicardConstruction q)
    (iota : E →+* K) (κ : K →+* ℂ) (he : κ.comp iota = P.μ) (N : ℕ) [NeZero N]
    (e : PEL.Objects.PELIso (C.pelObject iota κ he N) (C'.pelObject iota κ he N))

local instance : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance : IsIntegral W.abelian.toOver.left := W.abelian.variety.property
local instance : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance : Smooth W.abelian.toOver.hom := W.abelian.variety.presentation.smooth
local instance : IsMonHom (show M.abelian.toOver ⟶ W.abelian.toOver from e.polarized.abelian.hom) := e.polarized.abelianGroup

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction.ReferencePicardConstruction.referenceFieldIso_lattice (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    v ∈ P.lattice ↔ C.referenceFieldIso C' iota κ he N e v ∈ P.lattice := by
  have h := nativeRationalIso_integral_iff
    (show M.abelian.toOver ≅ W.abelian.toOver from e.polarized.abelian) (M.nativeReferenceMarking v)
  rw [← C.referenceFieldIso_marking, W.nativeReferenceMarking_integral, M.nativeReferenceMarking_integral] at h
  exact h.symm

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction.ReferencePicardConstruction.referencePELIso_level_exp (v : P.lattice) :
    HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints W.abelian.toOver)
      ((N : ℝ)⁻¹ • (W.nativeReferenceMarking (C.referenceFieldIso C' iota κ he N e v.val)).val) =
    HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints W.abelian.toOver) ((N : ℝ)⁻¹ • (W.nativeReferenceMarking v.val).val) := by
  let f : M.abelian.toOver ⟶ W.abelian.toOver := e.polarized.abelian.hom
  let : IsMonHom f := e.polarized.abelianGroup
  let a := LocallyConstant.const Foundations.Scheme.ProjectiveSpace.complexBase (Multiplicative.ofAdd (P.fixedLevelLabel hP N v))
  have h := e.polarized.level (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase) a
  change ((M.fixedFullLevel N).hom.app (.op (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) a).val ≫ e.polarized.abelian.hom =
    ((W.fixedFullLevel N).hom.app (.op (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) a).val at h
  dsimp only [a] at h
  rw [M.fixedFullLevel_native_reference, W.fixedFullLevel_native_reference] at h
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f
    (HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) ((N : ℝ)⁻¹ • (M.nativeReferenceMarking v.val).val)) = _ at h
  rw [Intrinsic.LiftDifferential.IntrinsicLinearMaps.linearLift_exp f] at h
  have hl := ((Intrinsic.Maps.IntrinsicLinearMaps.linearLift f).restrictScalars ℝ).map_smul (N : ℝ)⁻¹
    (M.nativeReferenceMarking v.val).val
  have hm := congrArg Subtype.val (C.referenceFieldIso_marking C' iota κ he N e v.val)
  change (W.nativeReferenceMarking (C.referenceFieldIso C' iota κ he N e v.val)).val =
    Intrinsic.Maps.IntrinsicLinearMaps.linearLift f (M.nativeReferenceMarking v.val).val at hm
  exact (congrArg (HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints W.abelian.toOver))
    (hl.trans (congrArg (fun x : RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel W.abelian => (N : ℝ)⁻¹ • x) hm.symm))).symm.trans h

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction.ReferencePicardConstruction.referenceFieldIso_level (v : P.lattice) :
    ∃ t ∈ P.lattice, C.referenceFieldIso C' iota κ he N e v.val - v.val = N • t := by
  let t : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E := (N : ℚ)⁻¹ • (C.referenceFieldIso C' iota κ he N e v.val - v.val)
  have ht : t ∈ P.lattice := by
    apply (W.nativeReferenceMarking_integral t).mp
    change (W.nativeReferenceMarking t).val ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice W.abelian
    have hv : (W.nativeReferenceMarking t).val =
        (N : ℝ)⁻¹ • (W.nativeReferenceMarking (C.referenceFieldIso C' iota κ he N e v.val)).val -
          (N : ℝ)⁻¹ • (W.nativeReferenceMarking v.val).val := by
      change (W.nativeReferenceMarking ((N : ℚ)⁻¹ • (C.referenceFieldIso C' iota κ he N e v.val - v.val))).val = _
      rw [map_smul, map_sub]
      change (N : ℚ)⁻¹ • ((W.nativeReferenceMarking (C.referenceFieldIso C' iota κ he N e v.val)).val -
        (W.nativeReferenceMarking v.val).val) = _
      rw [← IsScalarTower.algebraMap_smul ℝ ((N : ℚ)⁻¹), map_inv₀, map_natCast, smul_sub]
    rw [hv]
    change HodgeConjecture.DegreeTwo.ExponentialLocal.Constructions.Exponential.expAddHom (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints W.abelian.toOver) (_ - _) = 0
    rw [map_sub, sub_eq_zero]
    exact congrArg Additive.ofMul (C.referencePELIso_level_exp C' iota κ he N e v)
  refine ⟨t, ht, ?_⟩
  change C.referenceFieldIso C' iota κ he N e v.val - v.val = N • ((N : ℚ)⁻¹ • _)
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne N)), one_smul]

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction.ReferencePicardConstruction.referenceFieldIso_determinant (hN : 3 ≤ N) :
    LinearMap.det (C.referenceFieldIso C' iota κ he N e).toLinearMap = 1 := by
  have hspan : Submodule.span ℚ (P.lattice : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) = ⊤ := hP.2.2.2.2.2.2.2.2.2.1.2.1
  obtain ⟨a, ha, hd⟩ := RepresentationTheory.Theta.Geometric.LatticeDeterminantCongruence.lattice_determinant_congruence P.lattice (P.referenceBasis hP) hspan
    (C.referenceFieldIso C' iota κ he N e) N (by omega)
    (fun v hv => C.referenceFieldIso_level C' iota κ he N e ⟨v, hv⟩)
  exact DeterminantCongruence.norm_one_integral_congruence_eq_one _ a ha N hN hd
    (UnitaryDeterminant.unitary_det_norm_one P.b hP.2.2.1 (C.referenceFieldIso C' iota κ he N e)
      (C.referenceFieldIso_unitary C' iota κ he N e))

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction.ReferencePicardConstruction.referenceFieldIso_principal (hN : 3 ≤ N) :
    C.referenceFieldIso C' iota κ he N e ∈ Groups.principalSpecialUnitary P.b P.lattice N := by
  refine ⟨⟨C.referenceFieldIso_lattice C' iota κ he N e, fun v hv =>
    C.referenceFieldIso_level C' iota κ he N e ⟨v, hv⟩⟩,
    C.referenceFieldIso_unitary C' iota κ he N e, ?_⟩
  change LinearEquiv.det (C.referenceFieldIso C' iota κ he N e) = 1
  apply Units.ext
  simp only [LinearEquiv.coe_det, Units.val_one]
  exact C.referenceFieldIso_determinant C' iota κ he N e hN

end ReferencePicardConstruction

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PELArithmeticRecovery
