import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.ParameterDifferentials
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FiberSectionSupport
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FiberSectionNeighborhood
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TraceBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.SectionEvaluation

/-! # Point Parameter Kernel -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.PointParameterKernel

noncomputable section

/-! On the genuine component-selected principal source neighborhood,
the literal pulled-back parameters generate the original section ideal. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : Y ⟶ X) [IsFinite f.left] [Etale f.left]
  (s : Spec (CommRingCat.of R) ⟶ Y.left) (hs : s ≫ Y.hom = 𝟙 _)
  (U : X.left.Opens) (hUa : IsAffineOpen U) (hU : ⊤ ≤ (s ≫ f.left) ⁻¹ᵁ U)
  (hgood : TraceBasis.Good R Y X f U)

local instance sourceAlgebra : Algebra (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) :=
  AffineOpen.DeRhamTrace.sectionAlgebra R Y X f U

def component :
    letI : Algebra (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) R := IntegralComparison.Finite.SectionEvaluation.quotientAlgebra R X Y f s hs U hU
    R ⊗[IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U] IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U) := by
  letI : Algebra (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) R := IntegralComparison.Finite.SectionEvaluation.quotientAlgebra R X Y f s hs U hU
  letI : Module.Free (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) := hgood.2.2
  letI : Module.Finite (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) := f.left.finite_app U hUa
  letI : Algebra.Etale (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) :=
    AffineOpen.DeRhamTrace.sectionEtale R Y X f U hUa
  exact FiberSectionTrace.component (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) R
    (IntegralComparison.Finite.SectionEvaluation.evaluation R X Y f s hs U hU)

variable (z : IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U))
  (hz : letI : Algebra (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) R := IntegralComparison.Finite.SectionEvaluation.quotientAlgebra R X Y f s hs U hU
    ((1 : R) ⊗ₜ[IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U] z : R ⊗[IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U] IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) =
      component R X Y f s hs U hUa hU)

include hgood hz in
theorem contains : ⊤ ≤ s ⁻¹ᵁ Y.left.basicOpen z := by
  let : Algebra (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) R := IntegralComparison.Finite.SectionEvaluation.quotientAlgebra R X Y f s hs U hU
  let : Module.Free (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) := hgood.2.2
  let : Module.Finite (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) := f.left.finite_app U hUa
  let : Algebra.Etale (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) :=
    AffineOpen.DeRhamTrace.sectionEtale R Y X f U hUa
  have he := FiberSectionSupport.evaluation_lift
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) R
    (IntegralComparison.Finite.SectionEvaluation.evaluation R X Y f s hs U hU) z hz
  exact Intrinsic.SectionEvaluation.principal_contains R Y s hs (f.left ⁻¹ᵁ U) hU z he

variable [IsClosedImmersion s] [IsClosedImmersion (s ≫ f.left)]
  {g : ℕ} (t : Fin g → IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U)
  (ht : Ideal.span (Set.range t) = (s ≫ f.left).ker.ideal ⟨U,hUa⟩)

include hgood hz ht in
theorem ideal :
    Ideal.span (Set.range (ParameterDifferentials.parameters R X Y f U t z)) =
      s.ker.ideal ⟨Y.left.basicOpen z,(hUa.preimage f.left).basicOpen z⟩ := by
  let : Algebra (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) R := IntegralComparison.Finite.SectionEvaluation.quotientAlgebra R X Y f s hs U hU
  let : Module.Free (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) := hgood.2.2
  let : Module.Finite (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) := f.left.finite_app U hUa
  let : Algebra.Etale (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) :=
    AffineOpen.DeRhamTrace.sectionEtale R Y X f U hUa
  let : Algebra (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (Y.left.basicOpen z)) :=
    IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionAlgebra R Y (homOfLE (Y.left.basicOpen_le z))
  let : IsLocalization.Away z (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (Y.left.basicOpen z)) :=
    (hUa.preimage f.left).isLocalization_basicOpen z
  let ε : IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U) →ₐ[IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U] R :=
    IntegralComparison.Finite.SectionEvaluation.evaluation R X Y f s hs U hU
  let hc := contains R X Y f s hs U hUa hU hgood z hz
  let η := Intrinsic.SectionEvaluation.evaluation R Y s hs (Y.left.basicOpen z) hc
  have hη : η.toRingHom.comp
      (algebraMap (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (Y.left.basicOpen z))) =
      ε.toRingHom := by
    ext a
    exact Intrinsic.SectionEvaluation.restriction R Y s hs (f.left ⁻¹ᵁ U) hU
      (Y.left.basicOpen z) (Y.left.basicOpen_le z) hc a
  have hQ : RingHom.ker (algebraMap (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) R) = Ideal.span (Set.range t) := by
    change RingHom.ker (IntegralComparison.Finite.SectionEvaluation.targetEvaluation R X Y f s hs U hU).toRingHom = _
    exact (Intrinsic.SectionEvaluation.kernel R X (s ≫ f.left)
      (SectionEvaluationNaturality.image_retraction R Y X f s hs) U hU hUa).trans ht.symm
  have hk := FiberSectionNeighborhood.Trace.localized_parameter_kernel
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) R
    ε
    (IntegralComparison.Finite.SectionEvaluation.surjective R X Y f s hs U hU) z hz
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (Y.left.basicOpen z)) η.toRingHom hη t hQ
  change RingHom.ker η.toRingHom =
    Ideal.span (Set.range (ParameterDifferentials.parameters R X Y f U t z)) at hk
  exact hk.symm.trans (Intrinsic.SectionEvaluation.kernel R Y s hs (Y.left.basicOpen z) hc
    ((hUa.preimage f.left).basicOpen z))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.PointParameterKernel
