import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceFamilyFiberCoefficient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceHorizontalCycle

/-! # Source Fiber Contributing -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceFiberContributing

noncomputable section

/-! Every nonzero endpoint intersection contribution comes from the
finite native fiber-prime expansion. This rules out missing original
cycle coefficients when reindexing the local formula. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyOnSource.Family OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceFamilyFiberCoefficient.Family

theorem exists_prime (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)
    (m p : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (D : IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A))
    (hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ CompactHorizontalFamilyFiber.Family.parameter X A) ≫ Projective.FamilyIs.MatrixParameterOpen.affine)
      (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme D)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))
    (hDdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension D (SourceConstantFamily.FamilyRegularity.base X A) + p = m + 1)
    (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (B C : IrreducibleCloseds X.carrier)
    (hxD : Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C) ∈ (D : Set (Projective.FamilyOnSource.Family.space X A)))
    (F : Finset (PrimeSpectrum ((Projective.FamilyOnSource.Family.space X A).presheaf.stalk (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C)))))
    (hout : ∀ v, Foundations.Scheme.SupportDimension.supportTranscendenceDimension
        (Stalk.DivisorSupport.primeClosure (Projective.FamilyOnSource.Family.space X A) (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C)) v)
        (SourceConstantFamily.FamilyRegularity.base X A) = Foundations.Scheme.SupportDimension.supportTranscendenceDimension D (SourceConstantFamily.FamilyRegularity.base X A) - 1 →
      v ∉ F → FiltrationBaseLength.length
        ((Projective.FamilyOnSource.Family.space X A).presheaf.stalk (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C))) (Localization.AtPrime v.asIdeal)
        (.of _ (QuotSMulTop (Affine.ParameterFiber.germ ℂ (CompactHorizontalFamilyFiber.Family.parameter X A)
          (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C)) a)
          (CycleClass.Thom.IntersectionGeometry.localSupportModule (Projective.FamilyOnSource.Family.space X A) D (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C)) hxD))) = 0)
    (W : X.DimensionCycleSupport p) (hW : SourceHorizontalCycle.cycle X A D hη p a W ≠ 0)
    (hI : CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X W.val B C ≠ 0) :
    ∃ v ∈ F, SourceFamilyFiberCoefficient.Family.fiberSupport X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C) v = W.val := by
  let Z := Projective.FamilyOnSource.Family.space X A
  let x := CycleClass.Thom.IntersectionGeometry.supportPoint C
  let y := Projective.FamilyOnSource.Family.specialization X A a ha x
  let t := CompactHorizontalFamilyFiber.Family.parameter X A
  let r := Affine.ParameterFiber.germ ℂ t y a
  have hxW : x ∈ (W.val : Set X.carrier) := by
    by_contra hn
    apply hI
    exact dite_eq_right (fun h => hn h.1)
  let v := SourceFamilyFiberCoefficient.Primes.lift X A a ha x W.val hxW
  have hvW : SourceFamilyFiberCoefficient.Family.fiberSupport X A a ha x v = W.val := SourceFamilyFiberCoefficient.Primes.lift_support X A a ha x W.val hxW
  have hvim : Z.fromSpecStalk y v = Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint W.val) :=
    SourceFamilyFiberCoefficient.Primes.lift_image X A a ha x W.val hxW
  have hweight : GlobalParameterSum.Weights.weight Z (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint W.val))
      (Affine.ParameterFiber.germ ℂ t (Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint W.val)) a) D ≠ 0 := by
    rw [← SourceHorizontalCycle.coefficient X A D hη p a ha W]
    exact hW
  have hWD : Projective.FamilyOnSource.Family.specialization X A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint W.val) ∈ (D : Set Z) := by
    by_contra hn
    exact hweight (dite_eq_right hn)
  have hvD : v ∈ Module.support (Z.presheaf.stalk y) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z D y hxD) := by
    apply (GeometricSupportLocalization.mem_iff Z D y hxD v).mpr
    rw [hvim]
    exact hWD
  have hdim := SourceFamilyFiberCoefficient.Primes.dimension X A a ha x v (SourceFamilyFiberCoefficient.Primes.lift_kernel X A a ha x W.val hxW)
  rw [hvW] at hdim
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension W.val X.structureMap =
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure Z y v)
      (SourceConstantFamily.FamilyRegularity.base X A) at hdim
  have hWdim := Grading.supportDimension_add_codimension X m W.val
  rw [W.property] at hWdim
  have hvdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure Z y v)
      (SourceConstantFamily.FamilyRegularity.base X A) = Foundations.Scheme.SupportDimension.supportTranscendenceDimension D (SourceConstantFamily.FamilyRegularity.base X A) - 1 := by
    omega
  refine ⟨v, ?_, hvW⟩
  by_contra hvF
  have hz := hout v hvdim hvF
  have hr := SourceFamilyFiberCoefficient.Family.horizontal_nonzero Z D t hη y hxD a
  have he := IntrinsicParameterLength.Intrinsic.weight Z D t y hxD a v hvD hr
  rw [hz, ENat.toNat_zero, Nat.cast_zero] at he
  rw [hvim] at he
  exact hweight he.symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceFiberContributing
