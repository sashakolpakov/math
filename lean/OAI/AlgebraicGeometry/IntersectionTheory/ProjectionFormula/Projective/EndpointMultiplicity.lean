import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricEndpointSpecialization
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyIntrinsicQuotient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyRegularity
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.EndpointFiber
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.FiberIsolation
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.TorCutoff
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.Dimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ClosedComponents
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalParameterSum

/-! # Endpoint Multiplicity -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.EndpointMultiplicity

noncomputable section

/-! Actual projective endpoint intersection multiplicities are the
weighted native Tor coefficients of global family intersection
components. All local regularity, finite-resolution, quotient-module,
and isolated-support hypotheses are obtained from the family geometry. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace IsLocalRing

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.MatrixPath OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Polynomial.ProjectiveSubschemeFamily OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.ImmersionSupport

variable {n : ℕ} (A : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ)
  {Z₁ Z₂ : Scheme} [IsIntegral Z₁] [IsIntegral Z₂] [IsLocallyNoetherian Z₁] [IsLocallyNoetherian Z₂]
  (i₁ : Z₁ ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (i₂ : Z₂ ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n)
  (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
  (j₁ : Z₁ ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (j₂ : Z₂ ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n)
  [IsClosedImmersion j₁] [IsClosedImmersion j₂]
  (J₁ : Parameter.Polynomial.ProjectiveSubschemeFamily.space A i₁ ⟶ MatrixFamily.Family.space A)
  (J₂ : Parameter.Polynomial.ProjectiveSubschemeFamily.space A i₂ ⟶ MatrixFamily.Family.space A)
  [IsClosedImmersion J₁] [IsClosedImmersion J₂]
  (h₁ : j₁ ≫ MatrixFamily.Family.specialization A a ha = Parameter.Polynomial.ProjectiveSubschemeFamily.specialization A i₁ a ha ≫ J₁)
  (h₂ : j₂ ≫ MatrixFamily.Family.specialization A a ha = Parameter.Polynomial.ProjectiveSubschemeFamily.specialization A i₂ a ha ≫ J₂)
  (ht₁ : J₁ ≫ FamilyRegularity.IntegralFamilySupport.parameterLine A =
    Parameter.Polynomial.ProjectiveSubschemeFamily.parameter A i₁ ≫ Parameter.Polynomial.IntegralProduct.toLine A)
  (ht₂ : J₂ ≫ FamilyRegularity.IntegralFamilySupport.parameterLine A =
    Parameter.Polynomial.ProjectiveSubschemeFamily.parameter A i₂ ≫ Parameter.Polynomial.IntegralProduct.toLine A)
  (d : ℕ)
  (hproper : ∀ D : IrreducibleCloseds (Foundations.Scheme.ProjectiveSpace.projectiveSpace n),
    (D : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) ⊆
      (MatrixFamily.Family.specialization A a ha ⁻¹'
        (Closed.ImmersionSupport.support J₁ : Set (MatrixFamily.Family.space A))) ∩
      (MatrixFamily.Family.specialization A a ha ⁻¹'
        (Closed.ImmersionSupport.support J₂ : Set (MatrixFamily.Family.space A))) →
        d ≤ (Dimension.SpacePresentation.presentation n).supportCodimension D)

include h₁ h₂ ht₁ ht₂ hproper

theorem exists_sum (C : (Dimension.SpacePresentation.presentation n).DimensionCycleSupport d)
    (hx₁ : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (Closed.ImmersionSupport.support j₁ : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)))
    (hx₂ : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (Closed.ImmersionSupport.support j₂ : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n))) :
    let Y := MatrixFamily.Family.space A
    let x := CycleClass.Thom.IntersectionGeometry.supportPoint C.val
    let y := MatrixFamily.Family.specialization A a ha x
    let t := FamilyRegularity.IntegralFamilySupport.parameterLine A
    ∃ T : Finset (PrimeSpectrum (Y.presheaf.stalk y)),
      (∀ p ∈ T, Affine.ParameterFiber.germ ℂ t y a ∉ p.asIdeal ∧
        ∃ D : irreducibleComponents (IsolatedGeometricComponents.intersection Y (Closed.ImmersionSupport.support J₁) (Closed.ImmersionSupport.support J₂)),
          CycleClass.Thom.IntersectionGeometry.closedComponentSupport Y (IsolatedGeometricComponents.intersection Y (Closed.ImmersionSupport.support J₁) (Closed.ImmersionSupport.support J₂)) D =
            Stalk.DivisorSupport.primeClosure Y y p) ∧
      (∀ p, p ≠ closedPoint (Y.presheaf.stalk y) → p ∉ T →
        TotalTorCoefficient.coefficient Y (Closed.ImmersionSupport.support J₁) (Closed.ImmersionSupport.support J₂) (Y.fromSpecStalk y p) (n + 1) = 0) ∧
      CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity (Dimension.SpacePresentation.presentation n) (Closed.ImmersionSupport.support j₁) (Closed.ImmersionSupport.support j₂) C.val =
        ∑ p ∈ T, TotalTorCoefficient.coefficient Y (Closed.ImmersionSupport.support J₁) (Closed.ImmersionSupport.support J₂)
          (Y.fromSpecStalk y p) (n + 1) *
          ((Ring.ord ((Y.presheaf.stalk y) ⧸ p.asIdeal)
            (Ideal.Quotient.mk p.asIdeal (Affine.ParameterFiber.germ ℂ t y a))).toNat : ℚ) := by
  let X := Dimension.SpacePresentation.presentation n
  let Y := MatrixFamily.Family.space A
  let x := CycleClass.Thom.IntersectionGeometry.supportPoint C.val
  let u := MatrixFamily.Family.specialization A a ha
  let y := u x
  let t := FamilyRegularity.IntegralFamilySupport.parameterLine A
  let : IsClosedImmersion u := FamilySections.Family.ambient_closed A a ha
  obtain ⟨z₁, hz₁⟩ := (ProjectionFormula.Flat.ClosedSupport.support_range j₁ ▸ hx₁ : x ∈ Set.range j₁)
  obtain ⟨z₂, hz₂⟩ := (ProjectionFormula.Flat.ClosedSupport.support_range j₂ ▸ hx₂ : x ∈ Set.range j₂)
  have hy₁ : y ∈ (Closed.ImmersionSupport.support J₁ : Set Y) := by
    have hp : J₁ (Parameter.Polynomial.ProjectiveSubschemeFamily.specialization A i₁ a ha z₁) = y :=
      (congrArg (fun g : Z₁ ⟶ Y => g z₁) h₁.symm).trans (congrArg u hz₁)
    exact hp ▸ Closed.ImageStalkModule.mem J₁ (Parameter.Polynomial.ProjectiveSubschemeFamily.specialization A i₁ a ha z₁)
  have hy₂ : y ∈ (Closed.ImmersionSupport.support J₂ : Set Y) := by
    have hp : J₂ (Parameter.Polynomial.ProjectiveSubschemeFamily.specialization A i₂ a ha z₂) = y :=
      (congrArg (fun g : Z₂ ⟶ Y => g z₂) h₂.symm).trans (congrArg u hz₂)
    exact hp ▸ Closed.ImageStalkModule.mem J₂ (Parameter.Polynomial.ProjectiveSubschemeFamily.specialization A i₂ a ha z₂)
  let : Flat (J₁ ≫ t) := by rw [ht₁]; infer_instance
  let : Flat (J₂ ≫ t) := by rw [ht₂]; infer_instance
  let : Flat (CycleClass.Geometric.GenericPoint.reducedSupportι (Closed.ImmersionSupport.support J₁) ≫ t) := ProjectionFormula.Flat.ClosedSupport.flat J₁ t
  let : Flat (CycleClass.Geometric.GenericPoint.reducedSupportι (Closed.ImmersionSupport.support J₂) ≫ t) := ProjectionFormula.Flat.ClosedSupport.flat J₂ t
  have hyt : t y = Affine.ParameterFiber.point ℂ a := by
    have hyfiber : y ∈ FamilyRegularity.IntegralFamilySupport.parameterLine A ⁻¹'
        {Affine.ParameterFiber.point ℂ a} := by
      rw [← EndpointFiber.range A a ha]
      exact ⟨x, rfl⟩
    exact hyfiber
  let R := Y.presheaf.stalk y
  let S := (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).presheaf.stalk x
  let M := CycleClass.Thom.IntersectionGeometry.localSupportModule Y (Closed.ImmersionSupport.support J₁) y hy₁
  let N := CycleClass.Thom.IntersectionGeometry.localSupportModule Y (Closed.ImmersionSupport.support J₂) y hy₂
  let M₀ := CycleClass.Thom.IntersectionGeometry.localSupportModule (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (Closed.ImmersionSupport.support j₁) x hx₁
  let N₀ := CycleClass.Thom.IntersectionGeometry.localSupportModule (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (Closed.ImmersionSupport.support j₂) x hx₂
  let : HasProjectiveDimensionLE N (n + 1) := FamilyRegularity.Family.stalk_bound A y N
  let eM := FamilyIntrinsicQuotient.FamilyIntrinsic.equiv_at A i₁ a ha j₁ J₁ h₁ ht₁ z₁ x hz₁ hx₁ hy₁
  let eN := FamilyIntrinsicQuotient.FamilyIntrinsic.equiv_at A i₂ a ha j₂ J₂ h₂ ht₂ z₂ x hz₂ hx₂ hy₂
  have hiso := Proper.FiberIsolation.isolated X n d u t a (EndpointFiber.range A a ha)
    (Closed.ImmersionSupport.support J₁) (Closed.ImmersionSupport.support J₂) hproper C hy₁ hy₂
  obtain ⟨T, hT, hout, hsum⟩ := GeometricEndpointSpecialization.exists_sum Y t (Closed.ImmersionSupport.support J₁) (Closed.ImmersionSupport.support J₂)
    y hy₁ hy₂ a hyt S (u.stalkMap x).hom (u.stalkMap_surjective x)
    (FamilyStalkQuotient.Family.ambient_kernel A a ha x) M₀ N₀ eM eN (n + 1) hiso
  refine ⟨T, hT, hout, ?_⟩
  have he : Tor.Euler.euler S M₀ N₀ (n + 1) =
      CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (Closed.ImmersionSupport.support j₁) (Closed.ImmersionSupport.support j₂) C.val := by
    exact (Smooth.TorCutoff.euler_succ X.structureMap n x M₀ N₀).trans
      (GeometricTorCoefficient.intersectionMultiplicity X (Closed.ImmersionSupport.support j₁) (Closed.ImmersionSupport.support j₂) C.val hx₁ hx₂)
  exact he.symm.trans hsum

theorem global_sum (C : (Dimension.SpacePresentation.presentation n).DimensionCycleSupport d)
    (hx₁ : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (Closed.ImmersionSupport.support j₁ : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)))
    (hx₂ : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (Closed.ImmersionSupport.support j₂ : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n))) :
    let Y := MatrixFamily.Family.space A
    let y := MatrixFamily.Family.specialization A a ha (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
    let r := Affine.ParameterFiber.germ ℂ (FamilyRegularity.IntegralFamilySupport.parameterLine A) y a
    CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity (Dimension.SpacePresentation.presentation n) (Closed.ImmersionSupport.support j₁) (Closed.ImmersionSupport.support j₂) C.val =
      ∑ D ∈ Finite.ClosedComponents.components Y
        (IsolatedGeometricComponents.intersection Y (Closed.ImmersionSupport.support J₁) (Closed.ImmersionSupport.support J₂)),
        TotalTorCoefficient.coefficient Y (Closed.ImmersionSupport.support J₁) (Closed.ImmersionSupport.support J₂) (CycleClass.Thom.IntersectionGeometry.supportPoint D) (n + 1) *
          GlobalParameterSum.Weights.weight Y y r D := by
  let Y := MatrixFamily.Family.space A
  let x := CycleClass.Thom.IntersectionGeometry.supportPoint C.val
  let u := MatrixFamily.Family.specialization A a ha
  let y := u x
  let t := FamilyRegularity.IntegralFamilySupport.parameterLine A
  let r := Affine.ParameterFiber.germ ℂ t y a
  let c := fun D => TotalTorCoefficient.coefficient Y (Closed.ImmersionSupport.support J₁) (Closed.ImmersionSupport.support J₂) (CycleClass.Thom.IntersectionGeometry.supportPoint D) (n + 1)
  let F := Finite.ClosedComponents.components Y
    (IsolatedGeometricComponents.intersection Y (Closed.ImmersionSupport.support J₁) (Closed.ImmersionSupport.support J₂))
  have hyt : t y = Affine.ParameterFiber.point ℂ a := by
    have hyfiber : y ∈ FamilyRegularity.IntegralFamilySupport.parameterLine A ⁻¹'
        {Affine.ParameterFiber.point ℂ a} := by
      rw [← EndpointFiber.range A a ha]
      exact ⟨x, rfl⟩
    exact hyfiber
  have hr : r ∈ maximalIdeal (Y.presheaf.stalk y) :=
    (Affine.ParameterFiber.germ_mem_maximalIdeal ℂ t y a).mpr hyt
  obtain ⟨T, hT, hout, hsum⟩ := exists_sum A i₁ i₂ a ha j₁ j₂ J₁ J₂ h₁ h₂ ht₁ ht₂ d hproper C hx₁ hx₂
  have he := GlobalParameterSum.reindex Y y r hr c F T (by
    intro p hp
    exact ⟨(Finite.ClosedComponents.mem_iff Y _ _).mpr (hT p hp).2, (hT p hp).1⟩) (by
    intro p hp hpT
    change TotalTorCoefficient.coefficient Y (Closed.ImmersionSupport.support J₁) (Closed.ImmersionSupport.support J₂)
      (CycleClass.Thom.IntersectionGeometry.supportPoint (Stalk.DivisorSupport.primeClosure Y y p)) (n + 1) = 0
    rw [Stalk.DivisorSupport.primeClosure_point]
    exact hout p hp hpT)
  exact hsum.trans ((Finset.sum_congr rfl (fun p _ => by
    rw [show c (Stalk.DivisorSupport.primeClosure Y y p) =
        TotalTorCoefficient.coefficient Y (Closed.ImmersionSupport.support J₁) (Closed.ImmersionSupport.support J₂) (Y.fromSpecStalk y p) (n + 1) from
      congrArg (fun z => TotalTorCoefficient.coefficient Y (Closed.ImmersionSupport.support J₁) (Closed.ImmersionSupport.support J₂) z (n + 1))
        (Stalk.DivisorSupport.primeClosure_point Y y p)])).trans he)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.EndpointMultiplicity
