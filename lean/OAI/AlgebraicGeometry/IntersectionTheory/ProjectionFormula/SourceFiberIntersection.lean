import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceFiberContributing
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.MultiplicitySum
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports

/-! # Source Fiber Intersection -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceFiberIntersection

noncomputable section

section

/-! The full original endpoint-cycle pairing is the finite native
fiber-prime sum, including all possible nonzero contributions. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

namespace Pairing

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyOnSource.Family OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceFamilyFiberCoefficient.Family

theorem reindex (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)
    (m p : ℕ) [SmoothOfRelativeDimension m X.structureMap] (hp : p ≤ m)
    (D : IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A))
    (hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ CompactHorizontalFamilyFiber.Family.parameter X A) ≫ Projective.FamilyIs.MatrixParameterOpen.affine)
      (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme D)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))
    (hDdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension D (SourceConstantFamily.FamilyRegularity.base X A) + p = m + 1)
    (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (B C : IrreducibleCloseds X.carrier)
    (hxD : Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C) ∈ (D : Set (Projective.FamilyOnSource.Family.space X A)))
    (F : Finset (PrimeSpectrum ((Projective.FamilyOnSource.Family.space X A).presheaf.stalk (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C)))))
    (hF : ∀ v ∈ F, v ∈ Module.support ((Projective.FamilyOnSource.Family.space X A).presheaf.stalk (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C)))
        (CycleClass.Thom.IntersectionGeometry.localSupportModule (Projective.FamilyOnSource.Family.space X A) D (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C)) hxD) ∧
      Affine.ParameterFiber.germ ℂ (CompactHorizontalFamilyFiber.Family.parameter X A)
        (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C)) a ∈ v.asIdeal ∧
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension
        (Stalk.DivisorSupport.primeClosure (Projective.FamilyOnSource.Family.space X A) (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C)) v)
        (SourceConstantFamily.FamilyRegularity.base X A) = Foundations.Scheme.SupportDimension.supportTranscendenceDimension D (SourceConstantFamily.FamilyRegularity.base X A) - 1)
    (hout : ∀ v, Foundations.Scheme.SupportDimension.supportTranscendenceDimension
        (Stalk.DivisorSupport.primeClosure (Projective.FamilyOnSource.Family.space X A) (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C)) v)
        (SourceConstantFamily.FamilyRegularity.base X A) = Foundations.Scheme.SupportDimension.supportTranscendenceDimension D (SourceConstantFamily.FamilyRegularity.base X A) - 1 →
      v ∉ F → FiltrationBaseLength.length
        ((Projective.FamilyOnSource.Family.space X A).presheaf.stalk (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C))) (Localization.AtPrime v.asIdeal)
        (.of _ (QuotSMulTop (Affine.ParameterFiber.germ ℂ (CompactHorizontalFamilyFiber.Family.parameter X A)
          (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C)) a)
          (CycleClass.Thom.IntersectionGeometry.localSupportModule (Projective.FamilyOnSource.Family.space X A) D (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C)) hxD))) = 0) :
    (SourceHorizontalCycle.cycle X A D hη p a).sum
      (fun W c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X W.val B C) =
      ∑ v ∈ F, GlobalParameterSum.Weights.weight (Projective.FamilyOnSource.Family.space X A)
        ((Projective.FamilyOnSource.Family.space X A).fromSpecStalk (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C)) v)
        (Affine.ParameterFiber.germ ℂ (CompactHorizontalFamilyFiber.Family.parameter X A)
          ((Projective.FamilyOnSource.Family.space X A).fromSpecStalk (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C)) v) a) D *
        CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (SourceFamilyFiberCoefficient.Family.fiberSupport X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C) v) B C := by
  let Z := Projective.FamilyOnSource.Family.space X A
  let x := CycleClass.Thom.IntersectionGeometry.supportPoint C
  let y := Projective.FamilyOnSource.Family.specialization X A a ha x
  let t := CompactHorizontalFamilyFiber.Family.parameter X A
  have hk (v : F) : RingHom.ker ((Projective.FamilyOnSource.Family.specialization X A a ha).stalkMap x).hom ≤ v.val.asIdeal :=
    SourceFamilyFiberCoefficient.Primes.kernel_le X A a ha x v.val (hF v.val v.property).2.1
  have hgrade (v : F) : X.supportCodimension (SourceFamilyFiberCoefficient.Family.fiberSupport X A a ha x v.val) = p := by
    apply SourceFamilyFiberCoefficient.Primes.codimension X A a ha x m p v.val (hk v)
    rw [(hF v.val v.property).2.2]
    omega
  let V : F → X.DimensionCycleSupport p := fun v => ⟨SourceFamilyFiberCoefficient.Family.fiberSupport X A a ha x v.val, hgrade v⟩
  have hV : Function.Injective V := by
    intro v w he
    apply Subtype.ext
    exact SourceFamilyFiberCoefficient.Primes.injective X A a ha x v.val w.val (hk v) (hk w) (congrArg Subtype.val he)
  let b := SourceHorizontalCycle.cycle X A D hη p a
  let e := fun W : X.DimensionCycleSupport p => CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X W.val B C
  let w := fun v : PrimeSpectrum (Z.presheaf.stalk y) => GlobalParameterSum.Weights.weight Z (Z.fromSpecStalk y v)
    (Affine.ParameterFiber.germ ℂ t (Z.fromSpecStalk y v) a) D
  have hcoeff (v : F) (_ : v ∈ (Finset.univ : Finset F)) : b (V v) = w v.val := by
    rw [SourceHorizontalCycle.coefficient X A D hη p a ha]
    change GlobalParameterSum.Weights.weight Z (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint (SourceFamilyFiberCoefficient.Family.fiberSupport X A a ha x v.val)))
      (Affine.ParameterFiber.germ ℂ t (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint (SourceFamilyFiberCoefficient.Family.fiberSupport X A a ha x v.val))) a) D = _
    rw [SourceFamilyFiberCoefficient.Primes.support_image X A a ha x v.val (hk v)]
  have hmissing (W : X.DimensionCycleSupport p) (hW : W ∉ Finset.univ.image V) : b W * e W = 0 := by
    by_cases hb : b W = 0
    · rw [hb, zero_mul]
    by_cases he : e W = 0
    · rw [he, mul_zero]
    obtain ⟨v, hv, hvW⟩ := SourceFiberContributing.exists_prime X A m p D hη hDdim a ha B C hxD F hout W hb he
    exact (hW (Finset.mem_image.mpr ⟨⟨v, hv⟩, Finset.mem_univ _, Subtype.ext hvW⟩)).elim
  have he := Finite.MultiplicitySum.LocalCycle.reindex b e Finset.univ V hV (fun v => w v.val) hcoeff hmissing
  exact he.trans (Finset.sum_coe_sort F
    (fun v => w v * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (SourceFamilyFiberCoefficient.Family.fiberSupport X A a ha x v) B C))

end Pairing

end

section

/-! Proper endpoint intersections of an intrinsic horizontal family
with a fixed support are the fibers of one actual weighted family
cycle, and consequently have the same rational-equivalence class. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

namespace Horizontal

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyOnSource.Family

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)

def components (D : IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A)) (B : IrreducibleCloseds X.carrier) :=
  Finite.ClosedComponents.components (Projective.FamilyOnSource.Family.space X A) (IsolatedGeometricComponents.intersection (Projective.FamilyOnSource.Family.space X A)
    D (SourceConstantFamily.Family.support X A B))

def cycle (D : IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A)) (B : IrreducibleCloseds X.carrier)
    (m d : ℕ) (a : ℂ) : X.RationalDimensionCycle d :=
  SourceHorizontalCycle.weighted X A
    (fun E => TotalTorCoefficient.coefficient (Projective.FamilyOnSource.Family.space X A) D (SourceConstantFamily.Family.support X A B)
      (CycleClass.Thom.IntersectionGeometry.supportPoint E) (m + 1)) (components X A D B) d a

theorem coefficient (D : IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A)) (B : IrreducibleCloseds X.carrier)
    (m d : ℕ) (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (C : X.DimensionCycleSupport d) :
    cycle X A D B m d a C =
      ∑ E ∈ components X A D B,
        TotalTorCoefficient.coefficient (Projective.FamilyOnSource.Family.space X A) D (SourceConstantFamily.Family.support X A B)
          (CycleClass.Thom.IntersectionGeometry.supportPoint E) (m + 1) * GlobalParameterSum.Weights.weight (Projective.FamilyOnSource.Family.space X A)
          (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))
          (Affine.ParameterFiber.germ ℂ (CompactHorizontalFamilyFiber.Family.parameter X A)
            (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)) a) E :=
  SourceHorizontalCycle.weighted_coefficient X A _ _ d a ha C

theorem equivalent (D : IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A)) (B : IrreducibleCloseds X.carrier)
    (m d : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (a b : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (hb : (Polynomial.MatrixPath.determinant A).eval b ≠ 0) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X d (cycle X A D B m d a) (cycle X A D B m d b) :=
  SourceHorizontalCycle.weighted_equivalent X A _ _ m d a b ha hb

theorem support_subset (D : IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A))
    (hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ CompactHorizontalFamilyFiber.Family.parameter X A) ≫ Projective.FamilyIs.MatrixParameterOpen.affine)
      (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme D)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))
    (p : ℕ) (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (W : X.DimensionCycleSupport p) (hW : W ∈ (SourceHorizontalCycle.cycle X A D hη p a).support) :
    (W.val : Set X.carrier) ⊆ Projective.FamilyOnSource.Family.specialization X A a ha ⁻¹' (D : Set (Projective.FamilyOnSource.Family.space X A)) := by
  let S : Closeds X.carrier :=
    ⟨Projective.FamilyOnSource.Family.specialization X A a ha ⁻¹' (D : Set (Projective.FamilyOnSource.Family.space X A)), D.isClosed.preimage (Projective.FamilyOnSource.Family.specialization X A a ha).continuous⟩
  apply (Supports.supportPoint_mem_iff_subset S W.val).mp
  by_contra hn
  have hzero : SourceHorizontalCycle.cycle X A D hη p a W = 0 := by
    rw [SourceHorizontalCycle.coefficient X A D hη p a ha]
    exact dite_eq_right hn
  exact Finsupp.mem_support_iff.mp hW hzero

theorem coefficient_zero (D : IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A)) (B : IrreducibleCloseds X.carrier)
    (m d : ℕ) (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (C : X.DimensionCycleSupport d)
    (h : ¬ (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) ∈ (D : Set (Projective.FamilyOnSource.Family.space X A)) ∧
      CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (B : Set X.carrier))) : cycle X A D B m d a C = 0 := by
  rw [coefficient X A D B m d a ha]
  apply Finset.sum_eq_zero
  intro E hE
  have hs := Finite.ClosedComponents.subset (Projective.FamilyOnSource.Family.space X A)
    (IsolatedGeometricComponents.intersection (Projective.FamilyOnSource.Family.space X A) D (SourceConstantFamily.Family.support X A B)) E hE
  have hn : Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) ∉ (E : Set (Projective.FamilyOnSource.Family.space X A)) := by
    intro hy
    apply h
    refine ⟨(hs hy).1, ?_⟩
    have hb := (hs hy).2
    change Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) ∈
      (SourceConstantFamily.Family.support X A B : Set (Projective.FamilyOnSource.Family.space X A)) at hb
    rw [SourceConstantFamily.Family.support_coe] at hb
    have he : Projective.FamilyOnSource.Family.toSource X A (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)) = CycleClass.Thom.IntersectionGeometry.supportPoint C.val :=
      congrArg (fun g : X.carrier ⟶ X.carrier => g (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)) (Projective.FamilyOnSource.Family.specialization_source X A a ha)
    exact he ▸ hb
  rw [GlobalParameterSum.Weights.weight, dite_eq_right hn, mul_zero]

theorem pairing_zero (D : IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A))
    (hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ CompactHorizontalFamilyFiber.Family.parameter X A) ≫ Projective.FamilyIs.MatrixParameterOpen.affine)
      (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme D)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))
    (p : ℕ) (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (B C : IrreducibleCloseds X.carrier)
    (h : ¬ (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C) ∈ (D : Set (Projective.FamilyOnSource.Family.space X A)) ∧
      CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (B : Set X.carrier))) :
    (SourceHorizontalCycle.cycle X A D hη p a).sum
      (fun W c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X W.val B C) = 0 := by
  apply Finset.sum_eq_zero
  intro W hW
  have hs := support_subset X A D hη p a ha W hW
  have hz : CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X W.val B C = 0 := dite_eq_right (fun hc => h ⟨hs hc.1, hc.2⟩)
  exact mul_eq_zero_of_right _ hz

theorem isProper [IsIntegral X.carrier] (m p q : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (D : IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A))
    (hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ CompactHorizontalFamilyFiber.Family.parameter X A) ≫ Projective.FamilyIs.MatrixParameterOpen.affine)
      (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme D)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))
    (hDdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension D (SourceConstantFamily.FamilyRegularity.base X A) + p = m + 1)
    (B : X.DimensionCycleSupport q) (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (hproper : ∀ E : IrreducibleCloseds X.carrier,
      (E : Set X.carrier) ⊆ (Projective.FamilyOnSource.Family.specialization X A a ha ⁻¹' (D : Set (Projective.FamilyOnSource.Family.space X A))) ∩ (B.val : Set X.carrier) →
        p + q ≤ X.supportCodimension E) :
    CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X p q (SourceHorizontalCycle.cycle X A D hη p a)
      (Finsupp.single B 1) (cycle X A D B.val m (p + q) a) := by
  refine ⟨?_, ?_⟩
  · intro W hW B' hB' E hE
    have hB : B' = B := Finset.mem_singleton.mp (Finsupp.support_single_subset hB')
    subst B'
    apply hproper E
    have hs := support_subset X A D hη p a ha W hW
    intro z hz
    exact ⟨hs (hE hz).1, (hE hz).2⟩
  · intro C
    have hs : (SourceHorizontalCycle.cycle X A D hη p a).sum
        (fun W r => (Finsupp.single B (1 : ℚ)).sum (fun V s => r * s * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X W.val V.val C.val)) =
        (SourceHorizontalCycle.cycle X A D hη p a).sum (fun W r => r * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X W.val B.val C.val) := by
      apply Finset.sum_congr rfl
      intro W _
      dsimp only
      rw [Finsupp.sum_single_index (by simp), mul_one]
    rw [hs]
    by_cases h : Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) ∈ (D : Set (Projective.FamilyOnSource.Family.space X A)) ∧
        CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (B.val : Set X.carrier)
    · have hCd := Grading.supportDimension_add_codimension X m C.val
      rw [C.property] at hCd
      have hp : p ≤ m := by omega
      obtain ⟨F, hF, hout, he⟩ := SourceFamilyFiberCoefficient.Family.exists_sum X A m p q D hη hDdim B a ha hproper C h.1 h.2
      rw [coefficient X A D B.val m (p + q) a ha]
      exact he.trans (Pairing.reindex X A m p hp D hη hDdim a ha B.val C.val h.1 F hF hout).symm
    · rw [coefficient_zero X A D B.val m (p + q) a ha C h, pairing_zero X A D hη p a ha B.val C.val h]

end Horizontal

end

/-! Moving along an actual intrinsic source family preserves the
intersection with a fixed support whenever both full endpoint supports
meet it properly. Every family-component dimension is included. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace FamilyInvariance

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyOnSource.Family OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
  (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)
  (m p q : ℕ) [SmoothOfRelativeDimension m X.structureMap]
  (D : IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A))
  (hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ CompactHorizontalFamilyFiber.Family.parameter X A) ≫ Projective.FamilyIs.MatrixParameterOpen.affine)
    (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme D)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))
  (B : X.DimensionCycleSupport q)

theorem intersection_eq
    (hDdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension D (SourceConstantFamily.FamilyRegularity.base X A) + p = m + 1)
    (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (hproper : ∀ E : IrreducibleCloseds X.carrier,
      (E : Set X.carrier) ⊆ (Projective.FamilyOnSource.Family.specialization X A a ha ⁻¹' (D : Set (Projective.FamilyOnSource.Family.space X A))) ∩ (B.val : Set X.carrier) →
        p + q ≤ X.supportCodimension E) :
    Supports.ProperCycle.intersectionBilinear X m p q (SourceHorizontalCycle.cycle X A D hη p a) (Finsupp.single B 1) =
      Horizontal.cycle X A D B.val m (p + q) a := by
  have hc := Horizontal.isProper X A m p q D hη hDdim B a ha hproper
  exact CycleClass.Thom.IntersectionGeometry.isProperIntersectionCycle_unique X p q
    (Supports.ProperCycle.intersectionBilinear_isProper X m p q _ _ hc.1) hc

theorem equivalent (a b : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (hb : (Polynomial.MatrixPath.determinant A).eval b ≠ 0)
    (hproper_a : ∀ E : IrreducibleCloseds X.carrier,
      (E : Set X.carrier) ⊆ (Projective.FamilyOnSource.Family.specialization X A a ha ⁻¹' (D : Set (Projective.FamilyOnSource.Family.space X A))) ∩ (B.val : Set X.carrier) →
        p + q ≤ X.supportCodimension E)
    (hproper_b : ∀ E : IrreducibleCloseds X.carrier,
      (E : Set X.carrier) ⊆ (Projective.FamilyOnSource.Family.specialization X A b hb ⁻¹' (D : Set (Projective.FamilyOnSource.Family.space X A))) ∩ (B.val : Set X.carrier) →
        p + q ≤ X.supportCodimension E) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (p + q)
      (Supports.ProperCycle.intersectionBilinear X m p q (SourceHorizontalCycle.cycle X A D hη p a) (Finsupp.single B 1))
      (Supports.ProperCycle.intersectionBilinear X m p q (SourceHorizontalCycle.cycle X A D hη p b) (Finsupp.single B 1)) := by
  by_cases hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension D (SourceConstantFamily.FamilyRegularity.base X A) + p = m + 1
  · rw [intersection_eq X A m p q D hη B hd a ha hproper_a,
      intersection_eq X A m p q D hη B hd b hb hproper_b]
    exact Horizontal.equivalent X A D B.val m (p + q) a b ha hb
  · have hza : SourceHorizontalCycle.cycle X A D hη p a = 0 :=
      HorizontalFamilyGrading.Family.zero_of_dimension X A D hη m p hd a ha
    have hzb : SourceHorizontalCycle.cycle X A D hη p b = 0 :=
      HorizontalFamilyGrading.Family.zero_of_dimension X A D hη m p hd b hb
    rw [hza, hzb]
    exact CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X (p + q) _

end FamilyInvariance

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceFiberIntersection
