import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntrinsicFiberWeightedEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceConstantFamily
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceConstantQuotient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.StalkPrime
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.FiberIsolation
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceEndpointFiber
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricPrincipalQuotient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.PointClosureDimension

/-! # Source Family Fiber Coefficient -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceFamilyFiberCoefficient

noncomputable section

section

/-! An intrinsic horizontal family intersected with a constant support
has the expected native endpoint coefficient. Its two expansions use
the actual family-component weights and the original ThomClass fiber pairing. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Polynomial

namespace Family

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyOnSource.Family

theorem horizontal_nonzero (Z : Scheme) (D : IrreducibleCloseds Z)
    (t : Z ⟶ Spec (.of ℂ[X]))
    (hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ t) ≫ Projective.FamilyIs.MatrixParameterOpen.affine)
      (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme D)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))
    (x : Z) (hx : x ∈ (D : Set Z)) (a : ℂ) :
    Local.Principal.supportStalkMap Z D x hx (Affine.ParameterFiber.germ ℂ t x a) ≠ 0 := by
  rw [Affine.ParameterRestriction.support, ← Affine.ParameterComparison.germ]
  exact Projective.ParameterGerms.shiftedGerm_ne_zero _ hη _ _ a

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
  (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)

def fiberSupport (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (x : X.carrier) (v : PrimeSpectrum ((Projective.FamilyOnSource.Family.space X A).presheaf.stalk (Projective.FamilyOnSource.Family.specialization X A a ha x))) :
    IrreducibleCloseds X.carrier :=
  irreducibleSetEquivPoints.symm
    (Projective.FamilyOnSource.Family.toSource X A ((Projective.FamilyOnSource.Family.space X A).fromSpecStalk (Projective.FamilyOnSource.Family.specialization X A a ha x) v))

theorem exists_sum (m p q : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (D : IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A))
    (hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ CompactHorizontalFamilyFiber.Family.parameter X A) ≫ Projective.FamilyIs.MatrixParameterOpen.affine)
      (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme D)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))
    (hDdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension D (SourceConstantFamily.FamilyRegularity.base X A) + p = m + 1)
    (B : X.DimensionCycleSupport q) (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (hproper : ∀ E : IrreducibleCloseds X.carrier,
      (E : Set X.carrier) ⊆ (Projective.FamilyOnSource.Family.specialization X A a ha ⁻¹' (D : Set (Projective.FamilyOnSource.Family.space X A))) ∩ (B.val : Set X.carrier) →
        p + q ≤ X.supportCodimension E)
    (C : X.DimensionCycleSupport (p + q))
    (hxD : Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) ∈ (D : Set (Projective.FamilyOnSource.Family.space X A)))
    (hxB : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (B.val : Set X.carrier)) :
    let Z := Projective.FamilyOnSource.Family.space X A
    let x := CycleClass.Thom.IntersectionGeometry.supportPoint C.val
    let y := Projective.FamilyOnSource.Family.specialization X A a ha x
    let t := CompactHorizontalFamilyFiber.Family.parameter X A
    let r := Affine.ParameterFiber.germ ℂ t y a
    let B' := SourceConstantFamily.Family.support X A B.val
    ∃ F : Finset (PrimeSpectrum (Z.presheaf.stalk y)),
      (∀ v ∈ F, v ∈ Module.support (Z.presheaf.stalk y) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z D y hxD) ∧
        r ∈ v.asIdeal ∧
        Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure Z y v)
          (SourceConstantFamily.FamilyRegularity.base X A) = Foundations.Scheme.SupportDimension.supportTranscendenceDimension D (SourceConstantFamily.FamilyRegularity.base X A) - 1) ∧
      (∀ v, Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure Z y v)
          (SourceConstantFamily.FamilyRegularity.base X A) = Foundations.Scheme.SupportDimension.supportTranscendenceDimension D (SourceConstantFamily.FamilyRegularity.base X A) - 1 →
        v ∉ F → FiltrationBaseLength.length (Z.presheaf.stalk y) (Localization.AtPrime v.asIdeal)
          (.of _ (QuotSMulTop r (CycleClass.Thom.IntersectionGeometry.localSupportModule Z D y hxD))) = 0) ∧
      (∑ E ∈ ProjectionFormula.Finite.ClosedComponents.components Z (IsolatedGeometricComponents.intersection Z D B'),
        TotalTorCoefficient.coefficient Z D B' (CycleClass.Thom.IntersectionGeometry.supportPoint E) (m + 1) *
          GlobalParameterSum.Weights.weight Z y r E) =
        ∑ v ∈ F, GlobalParameterSum.Weights.weight Z (Z.fromSpecStalk y v)
          (Affine.ParameterFiber.germ ℂ t (Z.fromSpecStalk y v) a) D *
            CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (fiberSupport X A a ha x v) B.val C.val := by
  let Z := Projective.FamilyOnSource.Family.space X A
  let x := CycleClass.Thom.IntersectionGeometry.supportPoint C.val
  let u := Projective.FamilyOnSource.Family.specialization X A a ha
  let y := u x
  let t := CompactHorizontalFamilyFiber.Family.parameter X A
  let f := SourceConstantFamily.FamilyRegularity.base X A
  let r := Affine.ParameterFiber.germ ℂ t y a
  let B' := SourceConstantFamily.Family.support X A B.val
  let : IsIntegral Z := SourceConstantFamily.FamilyRegularity.integral X A
  let : SmoothOfRelativeDimension (m + 1) f := SourceConstantFamily.FamilyRegularity.totalDimension X A m
  let : IsClosedImmersion u := Projective.FamilySections.Family.source_closed X A a ha
  let : Flat t := inferInstanceAs
    (Flat (Parameter.Polynomial.ProjectiveSubschemeFamily.parameter A X.embedding ≫ Parameter.Polynomial.IntegralProduct.toLine A))
  have hux : Projective.FamilyOnSource.Family.toSource X A y = x := congrArg (fun g : X.carrier ⟶ X.carrier => g x)
    (Projective.FamilyOnSource.Family.specialization_source X A a ha)
  have hyB : y ∈ (B' : Set Z) := by
    change y ∈ (SourceConstantFamily.Family.support X A B.val : Set Z)
    rw [SourceConstantFamily.Family.support_coe]
    change Projective.FamilyOnSource.Family.toSource X A y ∈ (B.val : Set X.carrier)
    rw [hux]
    exact hxB
  have hcover : ∀ E : IrreducibleCloseds X.carrier,
      (E : Set X.carrier) ⊆ Proper.FiberIsolation.intersection X u D B' → p + q ≤ X.supportCodimension E := by
    intro E hE
    apply hproper E
    intro z hz
    have he := hE hz
    refine ⟨he.1, ?_⟩
    have hb : u z ∈ (SourceConstantFamily.Family.support X A B.val : Set Z) := he.2
    rw [SourceConstantFamily.Family.support_coe] at hb
    have hu : Projective.FamilyOnSource.Family.toSource X A (u z) = z := congrArg (fun g : X.carrier ⟶ X.carrier => g z)
      (Projective.FamilyOnSource.Family.specialization_source X A a ha)
    exact hu ▸ hb
  have hiso := Proper.FiberIsolation.isolated X m (p + q) u t a
    (SourceEndpointFiber.range X A a ha) D B' hcover C hxD hyB
  let R := Z.presheaf.stalk y
  let S := X.carrier.presheaf.stalk x
  let : Algebra R S := (u.stalkMap x).hom.toAlgebra
  let M := CycleClass.Thom.IntersectionGeometry.localSupportModule Z D y hxD
  let N := CycleClass.Thom.IntersectionGeometry.localSupportModule Z B' y hyB
  let N₀ := CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier B.val x hxB
  let : Module.Finite R M := Local.TorFinite.localSupportModule_finite Z D y hxD
  let : HasProjectiveDimensionLE N (m + 1) := SourceConstantFamily.FamilyRegularity.stalk_bound X A m y N
  have hi : Module.support R (QuotSMulTop r M) ∩ Module.support R N ⊆ {IsLocalRing.closedPoint R} := by
    intro v hv
    rw [Module.support_quotSMulTop] at hv
    apply hiso
    refine ⟨⟨hv.1.1, hv.2⟩, ?_⟩
    rw [Module.support_of_algebra, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
    exact Ideal.span_le.mpr hv.1.2
  have hr : Local.Principal.supportStalkMap Z D y hxD r ≠ 0 := horizontal_nonzero Z D t hη y hxD a
  have hBdim := SourceConstantFamily.Dimension.bound X A B.val
  have hCd := Grading.supportDimension_add_codimension X m C.val
  have hBd := Grading.supportDimension_add_codimension X m B.val
  rw [C.property] at hCd
  rw [B.property] at hBd
  have hyd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y) f =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension C.val X.structureMap := by
    have hd := Closed.PointClosureDimension.retraction u (Projective.FamilyOnSource.Family.toSource X A)
      (Projective.FamilyOnSource.Family.specialization_source X A a ha) X.structureMap x
    change Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y) f =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)) X.structureMap at hd
    have hCpoint : irreducibleSetEquivPoints.symm (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) = C.val :=
      irreducibleSetEquivPoints.symm_apply_apply C.val
    rw [hCpoint] at hd
    exact hd
  have heq : (Foundations.Scheme.SupportDimension.supportTranscendenceDimension D f - 1) +
      (Foundations.Scheme.SupportDimension.supportTranscendenceDimension B.val X.structureMap + 1) =
        (m + 1) + Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y) f := by
    rw [hyd]
    change Foundations.Scheme.SupportDimension.supportTranscendenceDimension D f + p = m + 1 at hDdim
    omega
  let eN := SourceConstantQuotient.equiv_at X A a ha B.val (CycleClass.Thom.IntersectionGeometry.supportPreimage B.val x hxB)
    x (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec B.val x hxB) hxB hyB
  have hk : RingHom.ker (algebraMap R S) = Ideal.span {r} := SourceConstantQuotient.ambient_kernel X A a ha x
  obtain ⟨F, hF, hout, he⟩ := IntrinsicFiberWeightedEuler.Intrinsic.exists_sum Z f (m + 1) t D B' y hxD hyB a hr
    S (u.stalkMap_surjective x) hk N₀ eN (Foundations.Scheme.SupportDimension.supportTranscendenceDimension B.val X.structureMap + 1) hBdim heq hi
  refine ⟨F, hF, hout, ?_⟩
  rw [← GeometricPrincipalQuotient.All.coefficient Z D B' y hxD hyB r hr (m + 1) hi, he]
  apply Finset.sum_congr rfl
  intro v hv
  apply congrArg (fun c : ℚ => GlobalParameterSum.Weights.weight Z (Z.fromSpecStalk y v)
    (Affine.ParameterFiber.germ ℂ t (Z.fromSpecStalk y v) a) D * c)
  have hvk : RingHom.ker (u.stalkMap x).hom ≤ v.asIdeal := by
    change RingHom.ker (algebraMap R S) ≤ v.asIdeal
    rw [hk]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hF v hv).2.1)
  have hs := Closed.StalkPrime.support_retraction u x v hvk (Projective.FamilyOnSource.Family.toSource X A) (Projective.FamilyOnSource.Family.specialization_source X A a ha)
  have htor := Closed.StalkPrime.euler u x v hvk B.val hxB (m + 1)
  rw [hs] at htor
  exact htor.trans (Closed.StalkPrime.projective_coefficient X m
    (fiberSupport X A a ha x v) B.val C.val (m + 1) (Nat.le_succ m))

end Family

end

/-! Stalk primes on a good source fiber correspond faithfully to
the actual supports on X, with the same geometric dimensions. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Primes

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyOnSource.Family OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceFamilyFiberCoefficient.Family

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)
  (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0) (x : X.carrier)

theorem kernel_le (v : PrimeSpectrum ((Projective.FamilyOnSource.Family.space X A).presheaf.stalk (Projective.FamilyOnSource.Family.specialization X A a ha x)))
    (hv : Affine.ParameterFiber.germ ℂ (CompactHorizontalFamilyFiber.Family.parameter X A)
      (Projective.FamilyOnSource.Family.specialization X A a ha x) a ∈ v.asIdeal) :
    RingHom.ker ((Projective.FamilyOnSource.Family.specialization X A a ha).stalkMap x).hom ≤ v.asIdeal := by
  rw [SourceConstantQuotient.ambient_kernel]
  exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hv)

theorem section_image (v : PrimeSpectrum ((Projective.FamilyOnSource.Family.space X A).presheaf.stalk (Projective.FamilyOnSource.Family.specialization X A a ha x)))
    (hv : RingHom.ker ((Projective.FamilyOnSource.Family.specialization X A a ha).stalkMap x).hom ≤ v.asIdeal) :
    Projective.FamilyOnSource.Family.specialization X A a ha (Projective.FamilyOnSource.Family.toSource X A ((Projective.FamilyOnSource.Family.space X A).fromSpecStalk (Projective.FamilyOnSource.Family.specialization X A a ha x) v)) =
      (Projective.FamilyOnSource.Family.space X A).fromSpecStalk (Projective.FamilyOnSource.Family.specialization X A a ha x) v := by
  let u := Projective.FamilyOnSource.Family.specialization X A a ha
  let : IsClosedImmersion u := Projective.FamilySections.Family.source_closed X A a ha
  have himage := Closed.StalkPrime.image u x v hv
  have hr (z : X.carrier) : Projective.FamilyOnSource.Family.toSource X A (u z) = z :=
    congrArg (fun g : X.carrier ⟶ X.carrier => g z) (Projective.FamilyOnSource.Family.specialization_source X A a ha)
  rw [← himage, hr]

theorem support_point (v : PrimeSpectrum ((Projective.FamilyOnSource.Family.space X A).presheaf.stalk (Projective.FamilyOnSource.Family.specialization X A a ha x))) :
    CycleClass.Thom.IntersectionGeometry.supportPoint (Family.fiberSupport X A a ha x v) =
      Projective.FamilyOnSource.Family.toSource X A ((Projective.FamilyOnSource.Family.space X A).fromSpecStalk (Projective.FamilyOnSource.Family.specialization X A a ha x) v) :=
  irreducibleSetEquivPoints.apply_symm_apply _

theorem support_image (v : PrimeSpectrum ((Projective.FamilyOnSource.Family.space X A).presheaf.stalk (Projective.FamilyOnSource.Family.specialization X A a ha x)))
    (hv : RingHom.ker ((Projective.FamilyOnSource.Family.specialization X A a ha).stalkMap x).hom ≤ v.asIdeal) :
    Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint (Family.fiberSupport X A a ha x v)) =
      (Projective.FamilyOnSource.Family.space X A).fromSpecStalk (Projective.FamilyOnSource.Family.specialization X A a ha x) v := by
  rw [support_point]
  exact section_image X A a ha x v hv

theorem injective (v w : PrimeSpectrum ((Projective.FamilyOnSource.Family.space X A).presheaf.stalk (Projective.FamilyOnSource.Family.specialization X A a ha x)))
    (hv : RingHom.ker ((Projective.FamilyOnSource.Family.specialization X A a ha).stalkMap x).hom ≤ v.asIdeal)
    (hw : RingHom.ker ((Projective.FamilyOnSource.Family.specialization X A a ha).stalkMap x).hom ≤ w.asIdeal)
    (h : Family.fiberSupport X A a ha x v = Family.fiberSupport X A a ha x w) : v = w := by
  apply ((Projective.FamilyOnSource.Family.space X A).fromSpecStalk (Projective.FamilyOnSource.Family.specialization X A a ha x)).isEmbedding.injective
  rw [← support_image X A a ha x v hv, ← support_image X A a ha x w hw, h]

theorem dimension (v : PrimeSpectrum ((Projective.FamilyOnSource.Family.space X A).presheaf.stalk (Projective.FamilyOnSource.Family.specialization X A a ha x)))
    (hv : RingHom.ker ((Projective.FamilyOnSource.Family.specialization X A a ha).stalkMap x).hom ≤ v.asIdeal) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Family.fiberSupport X A a ha x v) X.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension
        (Stalk.DivisorSupport.primeClosure (Projective.FamilyOnSource.Family.space X A) (Projective.FamilyOnSource.Family.specialization X A a ha x) v)
        (SourceConstantFamily.FamilyRegularity.base X A) := by
  let u := Projective.FamilyOnSource.Family.specialization X A a ha
  let : IsClosedImmersion u := Projective.FamilySections.Family.source_closed X A a ha
  have hd := Closed.PointClosureDimension.retraction u (Projective.FamilyOnSource.Family.toSource X A)
    (Projective.FamilyOnSource.Family.specialization_source X A a ha) X.structureMap
    (Projective.FamilyOnSource.Family.toSource X A ((Projective.FamilyOnSource.Family.space X A).fromSpecStalk (Projective.FamilyOnSource.Family.specialization X A a ha x) v))
  rw [section_image X A a ha x v hv] at hd
  exact hd.symm

theorem codimension (m p : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (v : PrimeSpectrum ((Projective.FamilyOnSource.Family.space X A).presheaf.stalk (Projective.FamilyOnSource.Family.specialization X A a ha x)))
    (hv : RingHom.ker ((Projective.FamilyOnSource.Family.specialization X A a ha).stalkMap x).hom ≤ v.asIdeal)
    (hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension
      (Stalk.DivisorSupport.primeClosure (Projective.FamilyOnSource.Family.space X A) (Projective.FamilyOnSource.Family.specialization X A a ha x) v)
      (SourceConstantFamily.FamilyRegularity.base X A) + p = m) :
    X.supportCodimension (Family.fiberSupport X A a ha x v) = p := by
  have h := Grading.supportDimension_add_codimension X m (Family.fiberSupport X A a ha x v)
  rw [dimension X A a ha x v hv] at h
  omega

def lift (W : IrreducibleCloseds X.carrier) (hx : x ∈ (W : Set X.carrier)) :
    PrimeSpectrum ((Projective.FamilyOnSource.Family.space X A).presheaf.stalk (Projective.FamilyOnSource.Family.specialization X A a ha x)) :=
  PrimeSpectrum.comap ((Projective.FamilyOnSource.Family.specialization X A a ha).stalkMap x).hom
    (Stalk.PrimeQuotient.kernelPrime X.carrier W x hx)

theorem lift_kernel (W : IrreducibleCloseds X.carrier) (hx : x ∈ (W : Set X.carrier)) :
    RingHom.ker ((Projective.FamilyOnSource.Family.specialization X A a ha).stalkMap x).hom ≤ (lift X A a ha x W hx).asIdeal :=
  Ideal.ker_le_comap ((Projective.FamilyOnSource.Family.specialization X A a ha).stalkMap x).hom

theorem lift_image (W : IrreducibleCloseds X.carrier) (hx : x ∈ (W : Set X.carrier)) :
    (Projective.FamilyOnSource.Family.space X A).fromSpecStalk (Projective.FamilyOnSource.Family.specialization X A a ha x) (lift X A a ha x W hx) =
      Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint W) := by
  have h := congrArg (fun g : Spec (X.carrier.presheaf.stalk x) ⟶ Projective.FamilyOnSource.Family.space X A =>
    g (Stalk.PrimeQuotient.kernelPrime X.carrier W x hx))
      (Scheme.SpecMap_stalkMap_fromSpecStalk (f := Projective.FamilyOnSource.Family.specialization X A a ha) (x := x))
  change (Projective.FamilyOnSource.Family.space X A).fromSpecStalk (Projective.FamilyOnSource.Family.specialization X A a ha x) (lift X A a ha x W hx) =
    Projective.FamilyOnSource.Family.specialization X A a ha (X.carrier.fromSpecStalk x (Stalk.PrimeQuotient.kernelPrime X.carrier W x hx)) at h
  rw [Stalk.PrimeQuotient.kernelPrime_image] at h
  exact h

theorem lift_support (W : IrreducibleCloseds X.carrier) (hx : x ∈ (W : Set X.carrier)) :
    Family.fiberSupport X A a ha x (lift X A a ha x W hx) = W := by
  apply irreducibleSetEquivPoints.injective
  change CycleClass.Thom.IntersectionGeometry.supportPoint (Family.fiberSupport X A a ha x (lift X A a ha x W hx)) = CycleClass.Thom.IntersectionGeometry.supportPoint W
  rw [support_point, lift_image]
  exact congrArg (fun g : X.carrier ⟶ X.carrier => g (CycleClass.Thom.IntersectionGeometry.supportPoint W)) (Projective.FamilyOnSource.Family.specialization_source X A a ha)

end Primes

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceFamilyFiberCoefficient
