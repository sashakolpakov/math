import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.PointParameterKernel
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.ParameterRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.CommonSectionPrincipalNeighborhood

/-! # Common Parameter Neighborhood -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.CommonParameterNeighborhood

noncomputable section

/-! Actual finite-source parameters admit pointed affine neighborhoods
with the same reduced open as a target neighborhood. The parameters
remain the literal restriction of the original finite pullback. -/
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
  {g : ℕ} (t : Fin g → IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U)

local instance sourceAlgebra : Algebra (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) :=
  AffineOpen.DeRhamTrace.sectionAlgebra R Y X f U

def parameters (V : Y.left.Opens) (hV : V ≤ f.left ⁻¹ᵁ U) : Fin g → IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y V :=
  AffineOpen.ParameterRestriction.parameters R Y (f.left ⁻¹ᵁ U) V hV
    (ParameterDifferentials.pullback R X Y f U t)

variable (Z : Scheme.{u}) (j₁ : Z ⟶ Y.left) (j₂ : Z ⟶ X.left)

structure Data where
  source : Y.left.affineOpens
  target : X.left.affineOpens
  source_le : source.val ≤ f.left ⁻¹ᵁ U
  target_le : target.val ≤ U
  source_contains : ⊤ ≤ s ⁻¹ᵁ source.val
  target_contains : ⊤ ≤ (s ≫ f.left) ⁻¹ᵁ target.val
  reduction : j₁ ⁻¹ᵁ source.val = j₂ ⁻¹ᵁ target.val
  ideal : Ideal.span (Set.range (parameters R X Y f U t source.val source_le)) = s.ker.ideal source
  regular : RingTheory.Sequence.IsWeaklyRegular (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y source.val)
    (List.ofFn (parameters R X Y f U t source.val source_le))
  basis : Module.Basis (Fin g) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y source.val) Ω[IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y source.val⁄R]
  basis_apply : ∀ a, basis a = KaehlerDifferential.D R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y source.val)
    (parameters R X Y f U t source.val source_le a)

variable [IsClosedImmersion s] [IsClosedImmersion (s ≫ f.left)]
  (ht : Ideal.span (Set.range t) = (s ≫ f.left).ker.ideal ⟨U,hUa⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (List.ofFn t))
  (b : Module.Basis (Fin g) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) Ω[IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U⁄R])
  (hb : ∀ a, b a = KaehlerDifferential.D R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (t a))
  {T₀ : Scheme.{u}} [Subsingleton T₀] [Nonempty T₀]
  (r : T₀ ⟶ Spec (CommRingCat.of R)) (hr : Function.Surjective r)
  (s₀ : T₀ ⟶ Z) [IsClosedImmersion j₁] [IsClosedImmersion j₂]
  (h₁ : s₀ ≫ j₁ = r ≫ s) (h₂ : s₀ ≫ j₂ = r ≫ (s ≫ f.left))

include hs hUa hU hgood ht hreg hb hr h₁ h₂ in
theorem exists_data : Nonempty (Data R X Y f s U t Z j₁ j₂) := by
  let : Algebra (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) R := IntegralComparison.Finite.SectionEvaluation.quotientAlgebra R X Y f s hs U hU
  let : Module.Free (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) := hgood.2.2
  let : Module.Finite (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) := f.left.finite_app U hUa
  let : Algebra.Etale (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) :=
    AffineOpen.DeRhamTrace.sectionEtale R Y X f U hUa
  let ε : IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U) →ₐ[IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U] R :=
    IntegralComparison.Finite.SectionEvaluation.evaluation R X Y f s hs U hU
  obtain ⟨z,hz,_,_⟩ := FiberSectionTrace.exists_lift
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) R ε
    (IntegralComparison.Finite.SectionEvaluation.surjective R X Y f s hs U hU)
  have hc := PointParameterKernel.contains R X Y f s hs U hUa hU hgood z hz
  have hi := PointParameterKernel.ideal R X Y f s hs U hUa hU hgood z hz t ht
  obtain ⟨a₁,a₂,ha₁,ha₂,he⟩ := CommonSectionPrincipalNeighborhood.exists_principal
    r hr s₀ j₁ j₂ s (s ≫ f.left) h₁ h₂ (Y.left.basicOpen z) U
    ((hUa.preimage f.left).basicOpen z) hUa hc hU
  let V₁ : Y.left.affineOpens := ⟨Y.left.basicOpen a₁,((hUa.preimage f.left).basicOpen z).basicOpen a₁⟩
  let V₂ : X.left.affineOpens := ⟨X.left.basicOpen a₂,hUa.basicOpen a₂⟩
  have hV : V₁.val ≤ f.left ⁻¹ᵁ U := (Y.left.basicOpen_le a₁).trans (Y.left.basicOpen_le z)
  have hp : parameters R X Y f U t V₁.val hV =
      AffineOpen.ParameterRestriction.parameters R Y (Y.left.basicOpen z) V₁.val
        (Y.left.basicOpen_le a₁) (ParameterDifferentials.parameters R X Y f U t z) := by
    funext a
    exact ConcreteCategory.congr_hom
      (Y.left.presheaf.map_comp (homOfLE (Y.left.basicOpen_le z)).op
        (homOfLE (Y.left.basicOpen_le a₁)).op) (f.left.app U (t a))
  have hfull : RingTheory.Sequence.IsWeaklyRegular (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U))
      (List.ofFn (ParameterDifferentials.pullback R X Y f U t)) := by
    change RingTheory.Sequence.IsWeaklyRegular (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U))
      (List.ofFn (fun a => algebraMap (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U)) (t a)))
    simpa only [List.map_ofFn, Function.comp_def] using hreg.of_flat (S := IntrinsicDeRham.SectionUnit.Intrinsic.ring R Y (f.left ⁻¹ᵁ U))
  refine ⟨{
    source := V₁
    target := V₂
    source_le := hV
    target_le := X.left.basicOpen_le a₂
    source_contains := ha₁
    target_contains := ha₂
    reduction := he
    ideal := ?_
    regular := AffineOpen.ParameterRestriction.regular R Y (f.left ⁻¹ᵁ U) V₁.val
      (hUa.preimage f.left) V₁.property hV _ hfull
    basis := AffineOpen.ParameterRestriction.basis R Y (f.left ⁻¹ᵁ U) V₁.val
      (hUa.preimage f.left) V₁.property hV (ParameterDifferentials.fullBasis R X Y f U hUa b)
    basis_apply := ?_ }⟩
  · rw [hp]
    exact AffineOpen.ParameterRestriction.span R Y (Y.left.basicOpen z) V₁.val
      ((hUa.preimage f.left).basicOpen z) V₁.property (Y.left.basicOpen_le a₁) _ s.ker hi
  · intro a
    exact AffineOpen.ParameterRestriction.basis_apply R Y (f.left ⁻¹ᵁ U) V₁.val
      (hUa.preimage f.left) V₁.property hV _
      (ParameterDifferentials.fullBasis R X Y f U hUa b)
      (ParameterDifferentials.fullBasis_apply R X Y f U hUa t b hb) a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.CommonParameterNeighborhood
