import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportOver

/-! # Support Square -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportSquare.BundleCycles

noncomputable section

section

/-! The reduced support of the open inverse image forms the actual
cartesian square with the original support and the ambient open immersion. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i]
    (B : IrreducibleCloseds Y) [Nonempty (SupportRestriction.BundleCycles.openSupportPullback i B)]

theorem openSupportIso_inv_inclusion :
    (SupportRestriction.BundleCycles.openSupportIso i B).inv ≫ SupportRestriction.BundleCycles.openSupportInclusion i B = CycleClass.Geometric.GenericPoint.reducedSupportι (SupportRestriction.BundleCycles.openRestrictedSupport i B) := by
  have h := congrArg (fun k => (SupportRestriction.BundleCycles.openSupportIso i B).inv ≫ k) (SupportRestriction.BundleCycles.openSupportIso_inclusion i B)
  exact h.symm.trans ((SupportRestriction.BundleCycles.openSupportIso i B).inv_hom_id_assoc _)

theorem openRestrictedSupport_isPullback :
    IsPullback (CycleClass.Geometric.GenericPoint.reducedSupportι (SupportRestriction.BundleCycles.openRestrictedSupport i B)) (SupportRestriction.BundleCycles.openRestrictedSupportMap i B) i (CycleClass.Geometric.GenericPoint.reducedSupportι B) :=
  IsPullback.of_iso_pullback ⟨(SupportRestriction.BundleCycles.openRestrictedSupportMap_inclusion i B).symm⟩
    (SupportRestriction.BundleCycles.openSupportIso i B).symm (openSupportIso_inv_inclusion i B) rfl

end

section

/-! The regular strata of the actual open-restricted support form the
cartesian square obtained by pasting the support and smooth-locus squares. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (i : X ⟶ Y) [IsOpenImmersion i.left] (B : IrreducibleCloseds Y.left)
    [Nonempty (SupportRestriction.BundleCycles.openSupportPullback i.left B)]

local notation "A" => OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportRestriction.BundleCycles.openRestrictedSupport i.left B

local instance : LocallyOfFiniteType (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X A).hom := CycleClass.Geometric.SupportFiniteType.supportStructureMap_locallyOfFiniteType A X.hom
local instance : LocallyOfFiniteType (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Y B).hom := CycleClass.Geometric.SupportFiniteType.supportStructureMap_locallyOfFiniteType B Y.hom
local instance : LocallyOfFinitePresentation (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X A).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (CycleClass.Geometric.SupportFiniteType.supportStructureMap A X.hom))
local instance : LocallyOfFinitePresentation (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Y B).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (CycleClass.Geometric.SupportFiniteType.supportStructureMap B Y.hom))

def openRegularSupportOverMap : CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X A ⟶ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver Y B := by
  let P : Over Foundations.Scheme.ProjectiveSpace.complexBase := CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X A
  let Q : Over Foundations.Scheme.ProjectiveSpace.complexBase := CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Y B
  let j : P ⟶ Q := SupportOver.BundleCycles.openRestrictedSupportOverMap i B
  let hP : LocallyOfFinitePresentation P.hom := inferInstance
  let hQ : LocallyOfFinitePresentation Q.hom := inferInstance
  let hj : IsOpenImmersion j.left := SupportOver.BundleCycles.openRestrictedSupportOverMap_open i B
  exact @RegularStratum.BundleCycles.openRegularStratumOverMap P Q hP hQ j hj

instance openRegularSupportOverMap_open : IsOpenImmersion (openRegularSupportOverMap i B).left :=
  inferInstanceAs (IsOpenImmersion (RegularStratum.BundleCycles.openRegularStratumMap (SupportOver.BundleCycles.openRestrictedSupportOverMap i B)))

theorem openRegularSupport_isPullback :
    IsPullback (openRegularSupportOverMap i B).left (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient X A).left
      (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient Y B).left i.left := by
  have hs := RegularStratum.BundleCycles.openRegularStratum_isPullback (SupportOver.BundleCycles.openRestrictedSupportOverMap i B)
  have ht := (openRestrictedSupport_isPullback i.left B).flip
  exact hs.paste_vert ht

theorem openRegularSupportOverMap_inclusion :
    openRegularSupportOverMap i B ≫ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient Y B = CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient X A ≫ i :=
  Over.OverMorphism.ext (openRegularSupport_isPullback i B).w

theorem openRegularSupport_range :
    Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient X A).left = i.left ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient Y B).left := by
  have h := Scheme.image_preimage_eq_of_isPullback (openRegularSupport_isPullback i B) Set.univ
  simpa only [Set.preimage_univ, Set.image_univ] using h

theorem openRegularInclusion_range :
    Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion X A) = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion Y B) := by
  have hx := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient X A)
  have hy := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient Y B)
  rw [hx, hy, openRegularSupport_range]
  rfl

end

section

/-! Restriction to an actual ambient open preserves the full support,
its regular locus, and the analytic singular boundary by exact inverse images. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (i : X ⟶ Y) [IsOpenImmersion i.left] (B : IrreducibleCloseds Y.left)
    [Nonempty (SupportRestriction.BundleCycles.openSupportPullback i.left B)]

local notation "A" => OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportRestriction.BundleCycles.openRestrictedSupport i.left B

omit [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] in
theorem openSupportInclusion_pointRange :
    Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X A) = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y B) := by
  rw [CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion_range, CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion_range]
  ext z
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying z ∈ (A : Set X.left) ↔ _
  rw [SupportRestriction.BundleCycles.openRestrictedSupport_coe]
  rfl

theorem openSupport_analyticBoundary :
    CycleClass.Thom.Scheme.RegularSupport.Constructions.analyticBoundary X A = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' CycleClass.Thom.Scheme.RegularSupport.Constructions.analyticBoundary Y B := by
  rw [CycleClass.Thom.Scheme.RegularSupport.Constructions.analyticBoundary_eq, CycleClass.Thom.Scheme.RegularSupport.Constructions.analyticBoundary_eq, openSupportInclusion_pointRange,
    openRegularInclusion_range, Set.preimage_sdiff]

theorem openSupport_regularAmbientOpen :
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X A : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen Y B : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) := by
  change (CycleClass.Thom.Scheme.RegularSupport.Constructions.analyticBoundary X A)ᶜ = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' (CycleClass.Thom.Scheme.RegularSupport.Constructions.analyticBoundary Y B)ᶜ
  rw [openSupport_analyticBoundary, Set.preimage_compl]

end

/-! The native models of an open-restricted integral support have the
same dimension as the original regular support, with actual norm-preserving
complex-linear coordinate identifications. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (i : X ⟶ Y) [IsOpenImmersion i.left] (B : IrreducibleCloseds Y.left)
    [Nonempty (SupportRestriction.BundleCycles.openSupportPullback i.left B)]

local notation "A" => OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportRestriction.BundleCycles.openRestrictedSupport i.left B

theorem openRestrictedRegular_dimension :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X A).hom =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver Y B).hom := by
  rw [CycleClass.Thom.Scheme.RegularSupport.Constructions.regularDimension_eq, CycleClass.Thom.Scheme.RegularSupport.Constructions.regularDimension_eq, SupportOver.BundleCycles.openRestrictedSupportOver_dimension]

def finiteModelCoordinatesOfEq (m n : ℕ) (h : m = n) : (Fin m → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
  h ▸ ContinuousLinearEquiv.refl ℂ (Fin m → ℂ)

theorem finiteModelCoordinatesOfEq_norm (m n : ℕ) (h : m = n) (v : Fin m → ℂ) :
    ‖finiteModelCoordinatesOfEq m n h v‖ = ‖v‖ := by
  subst n
  rfl

def openRestrictedRegularModelCoordinates : CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel Y B ≃L[ℂ] CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel X A :=
  finiteModelCoordinatesOfEq _ _ (openRestrictedRegular_dimension i B).symm

theorem openRestrictedRegularModelCoordinates_norm (v : CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel Y B) :
    ‖openRestrictedRegularModelCoordinates i B v‖ = ‖v‖ := finiteModelCoordinatesOfEq_norm _ _ _ v

include i in
theorem openImmersionOver_modelDimension [IsIntegral X.left] [IsIntegral Y.left] :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom = Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom := by
  rw [← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension X.hom,
    ← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension Y.hom]
  exact SupportOver.BundleCycles.openImmersionOver_dimension i

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportSquare.BundleCycles
