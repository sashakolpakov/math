import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PointParameterData
import OAI.NumberTheory.PadicHodge.IntegralComparison.CompositeSectionKernel
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionCompositeEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraEquivDifferentialBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.Ideal

/-! # Parameter Replacement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint

noncomputable section

/-! Any regular parameter basis for the actual section on the closed
chart has ambient lifts giving genuine projective point parameter data. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {N : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra PointParameterData.Chart.ambientAlgebra
variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R N)
  [IsClosedImmersion f.left] (z : Spec (CommRingCat.of R) ⟶ X.left) [IsClosedImmersion z]
  (hz : z ≫ X.hom = 𝟙 _) (g : ℕ) (U : (Projective.IntrinsicOverlap.Intrinsic.space R N).Opens) (hU : IsAffineOpen U)
  (D : PointParameterData.Chart.ParameterData X f z g U hU)
  (t : Fin g → Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))
  (ht : Ideal.span (Set.range t) = z.ker.ideal ⟨f.left ⁻¹ᵁ U,hU.preimage f.left⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular
    (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U)) (List.ofFn t))
  (b : Module.Basis (Fin g) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))
    Ω[Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U)⁄R])
  (hb : ∀ i, b i = KaehlerDifferential.D R _ (t i))

def PointParameterData.Chart.ParameterData.replace : PointParameterData.Chart.ParameterData X f z g U hU := by
  let a := (f.left.app U).hom
  let ha := f.left.app_surjective U hU
  let t' := CompositeSectionKernel.lift a ha t
  let e := Intrinsic.SmoothClosedSections.quotientEquiv R X (Projective.IntrinsicOverlap.Intrinsic.model R N) f U hU
  let ε := Intrinsic.SectionEvaluation.evaluation R X z hz (f.left ⁻¹ᵁ U) D.contains
  have hnormal : Ideal.span (Set.range D.equations) = RingHom.ker a := by
    simpa only [a, Scheme.Hom.ker_apply] using D.generates
  have htker : Ideal.span (Set.range t) = RingHom.ker ε.toRingHom :=
    ht.trans (Intrinsic.SectionEvaluation.kernel R X z hz (f.left ⁻¹ᵁ U) D.contains
      (hU.preimage f.left)).symm
  have hp : KoszulPartial.Resolution.pointIdeal Γ(Projective.IntrinsicOverlap.Intrinsic.space R N,U) D.equations t' =
      (z ≫ f.left).ker.ideal ⟨U,hU⟩ := by
    rw [KoszulPoint.Ideal.append]
    exact (CompositeSectionKernel.lifted_kernel a ha ε.toRingHom D.equations t hnormal htker).trans
      ((Intrinsic.SectionCompositeEvaluation.kernel R X (Projective.IntrinsicOverlap.Intrinsic.model R N) f z hz U D.contains).trans
        (Intrinsic.SectionEvaluation.kernel R (Projective.IntrinsicOverlap.Intrinsic.model R N) (z ≫ f.left)
          (Intrinsic.SectionCompositeEvaluation.over_base R X (Projective.IntrinsicOverlap.Intrinsic.model R N) f z hz) U D.contains hU))
  have hq (i : Fin g) : e.symm (t i) = Ideal.Quotient.mk (Projective.LocalAdjunction.ideal X f U hU) (t' i) := by
    apply e.injective
    rw [AlgEquiv.apply_symm_apply]
    exact (CompositeSectionKernel.lift_eq a ha t i).symm
  exact { D with
    parameters := t'
    quotientBasis := AlgebraEquivDifferentialBasis.basis e.symm b
    quotientBasis_apply := fun i =>
      (AlgebraEquivDifferentialBasis.basis_apply e.symm b t hb i).trans
        (congrArg (KaehlerDifferential.D R _) (hq i))
    point_generates := hp
    point_regular := CompositeSectionKernel.lifted_regular a ha D.equations t hnormal D.regular hreg }

omit [IsNoetherianRing R] in
theorem PointParameterData.Chart.ParameterData.replace_lift (i : Fin g) :
    f.left.app U ((D.replace X f z hz g U hU t ht hreg b hb).parameters i) = t i :=
  CompositeSectionKernel.lift_eq (f.left.app U).hom (f.left.app_surjective U hU) t i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint
