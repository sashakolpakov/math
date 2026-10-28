import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PELTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.HodgeScalarIsogenies
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ScaledMarkedPeriodTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELQuotients
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CrossPoincarePeriodMaps

/-! # Scaled PEL Quotients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.ScaledPELQuotients

noncomputable section

/-! Clearing a rational reference isometry gives an actual paired PEL
quotient between the original reference objects. The construction uses
the fixed reference period markings, Chern forms and full-level labels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.HodgeScalarIsogenies.IntrinsicLinearMaps

attribute [local implicit_reducible] AlgebraicModel.ReferenceAlgebraicModel.abelianScheme
  DualModel.ReferenceDualModel.abelianScheme PicardConstruction.ReferencePicardConstruction.polarized
  PicardConstruction.ReferencePicardConstruction.pelObject

local instance : IsLocallyNoetherian Foundations.Scheme.ProjectiveSpace.complexBase :=
  inferInstanceAs (IsLocallyNoetherian (Spec (.of ℂ)))

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z w : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {G : Fiber.ReferenceAnalyticFiber P w}
    {hP : P.IsAdmissible}

namespace ReferenceAlgebraicModel

variable (M : AlgebraicModel.ReferenceAlgebraicModel F hP) (W : AlgebraicModel.ReferenceAlgebraicModel G hP)

local instance : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance : IsIntegral W.abelian.toOver.left := W.abelian.variety.property
local instance : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance : Smooth W.abelian.toOver.hom := W.abelian.variety.presentation.smooth

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceTransport_symm (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    (M.nativeReferenceTransport W g).symm = W.nativeReferenceTransport M g.symm := rfl

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.scaledReferenceTransport_integral (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (D : ℕ)
    (m : P.lattice →ₗ[ℤ] P.lattice)
    (hm : ∀ x : P.lattice, (m x).val = D • g x.val)
    (x : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) (hx : x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods M.abelian) :
    D • M.nativeReferenceTransport W g x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods W.abelian := by
  obtain ⟨u, rfl⟩ := M.nativeReferenceMarking.surjective x
  have hu : u ∈ P.lattice := (M.nativeReferenceMarking_integral u).mp hx
  rw [M.nativeReferenceTransport_marking, ← map_nsmul]
  apply (W.nativeReferenceMarking_integral _).mpr
  rw [← hm ⟨u, hu⟩]
  exact (m ⟨u, hu⟩).property

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.exists_scaled_reference_isogenies
    (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hg : g ∈ Groups.unitarySubgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b))
    (hw : w.val = P.lineAction g z.val) (D : ℕ) (hD : 0 < D)
    (m m' : P.lattice →ₗ[ℤ] P.lattice)
    (hm : ∀ x : P.lattice, (m x).val = D • g x.val)
    (hm' : ∀ x : P.lattice, (m' x).val = D • g.symm x.val) :
    ∃ (f : HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny M.abelianScheme W.abelianScheme)
      (v : HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny W.abelianScheme M.abelianScheme),
      Etale f.hom.left ∧ Etale v.hom.left ∧
      f.hom ≫ v.hom = (𝟙 M.abelianScheme.scheme) ^ (D ^ 2) ∧
      v.hom ≫ f.hom = (𝟙 W.abelianScheme.scheme) ^ (D ^ 2) ∧
      (∀ u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f.hom (M.nativeReferenceMarking u) =
        W.nativeReferenceMarking (D • g u)) ∧
      (∀ a, M.integralAction.map a ≫ f.hom = f.hom ≫ W.integralAction.map a) := by
  let e := M.nativeReferenceTransport W g
  let q := D • e.toLinearMap
  let r := D • e.symm.toLinearMap
  have hq : ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure M.abelian)
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure W.abelian) q :=
    ScaledMarkedPeriodTransport.isHodgeMap_nsmul (M.nativeReferenceTransport_hodge W g hg hw) D
  have hr : ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure W.abelian)
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure M.abelian) r :=
    ScaledMarkedPeriodTransport.isHodgeMap_nsmul (M.nativeReferenceTransport_inverse_hodge W g hg hw) D
  have hqΛ : ∀ x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods M.abelian, q x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods W.abelian :=
    M.scaledReferenceTransport_integral W g D m hm
  have hrΛ : ∀ x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods W.abelian, r x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods M.abelian := by
    intro x hx
    change D • (M.nativeReferenceTransport W g).symm x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods M.abelian
    rw [M.nativeReferenceTransport_symm]
    exact W.scaledReferenceTransport_integral M g.symm D m' hm' x hx
  have hqr : r.comp q = D ^ 2 • (LinearMap.id : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian →ₗ[ℚ] _) := by
    apply LinearMap.ext
    intro x
    change D • e.symm (D • e x) = D ^ 2 • x
    rw [map_nsmul, e.symm_apply_apply, smul_smul, pow_two]
  have hrq : q.comp r = D ^ 2 • (LinearMap.id : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods W.abelian →ₗ[ℚ] _) := by
    apply LinearMap.ext
    intro x
    change D • e (D • e.symm x) = D ^ 2 • x
    rw [map_nsmul, e.apply_symm_apply, smul_smul, pow_two]
  obtain ⟨hf, hfe, hfs, hv, hve, hvs⟩ :=
    Integral.HodgeScalarIsogenies.IntrinsicLinearMaps.nativeIntegralHodgeMaps_both_finite_etale q r hq hr hqΛ hrΛ
      (D ^ 2) (pow_pos hD 2) hqr hrq
  let := hfe
  let := hve
  let f : HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny M.abelianScheme W.abelianScheme := {
    hom := Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend q hq hqΛ
    preservesGroup := inferInstance
    finite := hf
    flat := inferInstance
    surjective := hfs }
  let v : HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny W.abelianScheme M.abelianScheme := {
    hom := Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend r hr hrΛ
    preservesGroup := inferInstance
    finite := hv
    flat := inferInstance
    surjective := hvs }
  refine ⟨f, v, hfe, hve,
    Integral.HodgeScalarIsogenies.IntrinsicLinearMaps.nativeIntegralHodgeMaps_scalar_composition q r hq hr hqΛ hrΛ (D ^ 2) hqr,
    Integral.HodgeScalarIsogenies.IntrinsicLinearMaps.nativeIntegralHodgeMaps_scalar_composition r q hr hq hrΛ hqΛ (D ^ 2) hrq, ?_, ?_⟩
  · intro u
    change Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend q hq hqΛ) (M.nativeReferenceMarking u) = _
    rw [Intrinsic.HodgeFullness.IntrinsicLinearMaps.rationalLift_nativeHodgeDescend]
    change D • M.nativeReferenceTransport W g (M.nativeReferenceMarking u) = _
    rw [M.nativeReferenceTransport_marking, map_nsmul]
  · intro a
    apply Integral.HodgeScalarIsogenies.IntrinsicLinearMaps.nativeIntegralHodgeMap_intertwines q hq hqΛ
    have h := M.nativeReferenceTransport_action W g a
    change e.toLinearMap.comp (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (M.integralAction.map a)) =
      (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (W.integralAction.map a)).comp e.toLinearMap at h
    apply LinearMap.ext
    intro x
    change D • e (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (M.integralAction.map a) x) =
      Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (W.integralAction.map a) (D • e x)
    rw [map_nsmul]
    exact congrArg (fun v => D • v) (LinearMap.congr_fun h x)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.referenceMap_level
    (f : M.abelianScheme.scheme ⟶ W.abelianScheme.scheme) [IsMonHom f]
    (N : ℕ) [NeZero N] (m : P.lattice →ₗ[ℤ] P.lattice)
    (hm : ∀ u : P.lattice, Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f (M.nativeReferenceMarking u.val) =
      W.nativeReferenceMarking (m u).val)
    (hcongr : ∀ u : P.lattice, ∃ t : P.lattice, m u - u = N • t)
    (T : Over Foundations.Scheme.ProjectiveSpace.complexBase) (c : LocallyConstant T.left (Frame.Labels.LevelCover.Coefficients (3 * s) N)) :
    ((M.fixedFullLevel N).hom.app (.op T) c).val ≫ f =
      ((W.fixedFullLevel N).hom.app (.op T) c).val := by
  apply Level.Stabilizers.LevelCover.level_comparison_of_base_constants (M.fixedFullLevel N) (W.fixedFullLevel N)
    f ?_ T c
  intro a
  obtain ⟨u, hu⟩ := P.fixedLevelLabel_surjective hP N a.toAdd
  have hpoint :
      (((M.fixedFullLevel N).hom.app (.op (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)))
        (LocallyConstant.const Foundations.Scheme.ProjectiveSpace.complexBase (Multiplicative.ofAdd (P.fixedLevelLabel hP N u)))).val ≫ f =
      (((W.fixedFullLevel N).hom.app (.op (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)))
        (LocallyConstant.const Foundations.Scheme.ProjectiveSpace.complexBase (Multiplicative.ofAdd (P.fixedLevelLabel hP N (m u))))).val := by
    rw [M.fixedFullLevel_native_reference, W.fixedFullLevel_native_reference]
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f
      (HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
        ((N : ℝ)⁻¹ • (M.nativeReferenceMarking u.val).val)) = _
    rw [Intrinsic.LiftDifferential.IntrinsicLinearMaps.linearLift_exp]
    have hs := ((Intrinsic.Maps.IntrinsicLinearMaps.linearLift f).restrictScalars ℝ).map_smul
      (N : ℝ)⁻¹ (M.nativeReferenceMarking u.val).val
    exact congrArg (HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints W.abelian.toOver))
      (hs.trans (congrArg (fun x : RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel W.abelian => (N : ℝ)⁻¹ • x)
        (congrArg Subtype.val (hm u))))
  rw [P.fixedLevelLabel_congruent hP N u (m u) (hcongr u), hu] at hpoint
  exact hpoint

end ReferenceAlgebraicModel

namespace ReferencePicardConstruction

variable {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {W : AlgebraicModel.ReferenceAlgebraicModel G hP}
    {A : DualModel.ReferenceDualModel F hP} {B : DualModel.ReferenceDualModel G hP}
    {p : IsogenyKernel.ReferenceLatticeIsogeny M A} {q : IsogenyKernel.ReferenceLatticeIsogeny W B}
    (C : PicardConstruction.ReferencePicardConstruction p) (C' : PicardConstruction.ReferencePicardConstruction q)

local instance : IsMonHom (show M.abelian.toOver ⟶ A.abelian.toOver from p.isogeny.hom) :=
  p.isogeny.preservesGroup
local instance : IsMonHom (show W.abelian.toOver ⟶ B.abelian.toOver from q.isogeny.hom) :=
  q.isogeny.preservesGroup

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction.ReferencePicardConstruction.polarizationPullback_of_reference_chern
    (f : M.abelianScheme.scheme ⟶ W.abelianScheme.scheme) [IsMonHom f] (n : ℕ)
    (hf : ∀ x y, Intrinsic.ChernPairing.nativeChernForm W.abelian C'.ampleLine (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f x) (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f y) =
      n • Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine x y) :
    AbelianScheme.FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom f C.dual C'.dual C'.polarization = p.isogeny.hom ^ n := by
  let d : B.abelian.toOver ⟶ A.abelian.toOver := AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f C.dual C'.dual
  let : IsMonHom d := AbelianScheme.IsogenyQuotient.Noetherian.DualMaps.Construction.noetherian_nativeDualMap_isMonHom f C.dual C'.dual
  have hdual (x : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B.abelian) (y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) :
      C.referencePeriodPairing (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift d x) y =
        C'.referencePeriodPairing x (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f y) := by
    have hA := RepresentationTheory.Theta.Geometric.LinePeriodPairing.linePeriodPairing_pullback B.abelian M.abelian A.abelian M.abelian
      d (𝟙 M.abelian.toOver) (HilbertConstruction.Line.Bundles.LineBundle.classOf C.poincare) x y
    have hB := RepresentationTheory.Theta.Geometric.LinePeriodPairing.linePeriodPairing_pullback B.abelian M.abelian B.abelian W.abelian
      (𝟙 B.abelian.toOver) f (HilbertConstruction.Line.Bundles.LineBundle.classOf C'.poincare) x y
    rw [Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_id] at hA hB
    exact hA.symm.trans ((congrArg (fun L => RepresentationTheory.Theta.Geometric.LinePeriodPairing.linePeriodPairing B.abelian M.abelian L x y)
      (AbelianScheme.IsogenyQuotient.Noetherian.DualPoincare.Construction.noetherian_nativeDualMap_poincare C.dual C'.dual f)).trans hB)
  change f ≫ q.isogeny.hom ≫ d = p.isogeny.hom ^ n
  apply C.referencePeriodPairing_detects M.abelian
  intro x y
  rw [Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, Intrinsic.MultiplicationPeriods.IntrinsicLinearMaps.rationalLift_pow]
  simp only [LinearMap.comp_apply, LinearMap.smul_apply]
  rw [hdual, C'.referencePeriodPairing_isogeny, map_nsmul, LinearMap.smul_apply,
    C.referencePeriodPairing_isogeny]
  exact hf x y

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction.ReferencePicardConstruction.exists_paired_quotient_of_scaled_reference_transport
    {K : Type} [Field K] [CharZero K]
    (iota : E →+* K) (κ : K →+* ℂ) (he : κ.comp iota = P.μ)
    (N : ℕ) [NeZero N]
    (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hg : g ∈ Groups.unitarySubgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b))
    (hw : w.val = P.lineAction g z.val) (D : ℕ) (hD : 0 < D)
    (hmod : Nat.ModEq N (D ^ 2) 1) (m m' : P.lattice →ₗ[ℤ] P.lattice)
    (hm : ∀ x : P.lattice, (m x).val = D • g x.val)
    (hm' : ∀ x : P.lattice, (m' x).val = D • g.symm x.val)
    (hcongr : ∀ u : P.lattice, ∃ t : P.lattice, m u - u = N • t) :
    Nonempty (Paired.PELQuotients.PairedPELQuotient (C.pelObject iota κ he N) (C'.pelObject iota κ he N) (D ^ 2)) := by
  let : IsLocallyNoetherian (Over.mk (Spec.map (CommRingCat.ofHom κ))).left :=
    inferInstanceAs (IsLocallyNoetherian Foundations.Scheme.ProjectiveSpace.complexBase)
  obtain ⟨f, v, hfe, _, hfv, hvf, hperiod, haction⟩ :=
    M.exists_scaled_reference_isogenies W g hg hw D hD m m' hm hm'
  have hchern (x y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) :
      Intrinsic.ChernPairing.nativeChernForm W.abelian C'.ampleLine (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f.hom x) (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f.hom y) =
        D ^ 2 • Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine x y := by
    obtain ⟨u, rfl⟩ := M.nativeReferenceMarking.surjective x
    obtain ⟨t, rfl⟩ := M.nativeReferenceMarking.surjective y
    simp only [hperiod, map_nsmul, LinearMap.smul_apply]
    rw [C'.chern, C.chern]
    have htrace : P.traceForm (g u) (g t) = P.traceForm u t :=
      congrArg (fun b : E => (P.denominator : ℚ) * Algebra.trace ℚ E (P.imaginaryScalar * b))
        (hg u t)
    rw [htrace, smul_smul, pow_two]
  let fPEL : AbelianScheme.IsogenyQuotient.Intrinsic.PELBaseChange.Construction.NativePELQuotient (C.pelObject iota κ he N) (C'.pelObject iota κ he N) (D ^ 2) := {
    isogeny := f
    etale := hfe
    polarization := C.polarizationPullback_of_reference_chern C' f.hom (D ^ 2) hchern
    action := fun a => (haction a).symm
    marking := M.referenceMap_level W f.hom N m (fun u =>
      (hperiod u.val).trans (congrArg W.nativeReferenceMarking (hm u).symm)) hcongr }
  let vPEL := Paired.PELQuotients.scalarComplementPELQuotient fPEL v (pow_pos hD 2) hmod hfv hvf
  exact ⟨{
    forward := fPEL
    reverse := vPEL
    forward_reverse := hfv
    reverse_forward := hvf }⟩

end ReferencePicardConstruction

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.reference_paired_quotient_of_scaled_isometry
    {K : Type} [Field K] [CharZero K]
    (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible) (z w : P.domain)
    (iota : E →+* K) (κ : K →+* ℂ) (he : κ.comp iota = P.μ)
    (N : ℕ) [NeZero N]
    (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hg : g ∈ Groups.unitarySubgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b))
    (hw : w.val = P.lineAction g z.val) (D : ℕ) (hD : 0 < D)
    (hmod : Nat.ModEq N (D ^ 2) 1) (m m' : P.lattice →ₗ[ℤ] P.lattice)
    (hm : ∀ x : P.lattice, (m x).val = D • g x.val)
    (hm' : ∀ x : P.lattice, (m' x).val = D • g.symm x.val)
    (hcongr : ∀ u : P.lattice, ∃ t : P.lattice, m u - u = N • t) :
    Nonempty (Paired.PELQuotients.PairedPELQuotient (P.referencePELObject hP z iota κ he N)
      (P.referencePELObject hP w iota κ he N) (D ^ 2)) := by
  let F := Fiber.referenceAnalyticFiber P hP z
  let G := Fiber.referenceAnalyticFiber P hP w
  let M := AlgebraicModel.referenceAlgebraicModel F hP
  let W := AlgebraicModel.referenceAlgebraicModel G hP
  let A := DualModel.referenceDualModel F hP
  let B := DualModel.referenceDualModel G hP
  let p := (IsogenyKernel.referenceLatticeIsogeny_nonempty M A).some
  let q := (IsogenyKernel.referenceLatticeIsogeny_nonempty W B).some
  let C := (PicardConstruction.referencePicardConstruction_nonempty p).some
  let C' := (PicardConstruction.referencePicardConstruction_nonempty q).some
  exact C.exists_paired_quotient_of_scaled_reference_transport C'
    iota κ he N g hg hw D hD hmod m m' hm hm' hcongr

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.ScaledPELQuotients
