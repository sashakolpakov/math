import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntrinsicPrincipalDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntrinsicParameterLength
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FiberPrimeTor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.AffineParameter

/-! # Intrinsic Fiber Weighted Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntrinsicFiberWeightedEuler

noncomputable section

/-! On a smooth parameter family, the principal quotient's Euler
pairing is the finite sum of actual divisor weights times native Tor
pairings on the scalar fiber. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Polynomial

namespace Intrinsic

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

theorem exists_sum (Z : Scheme) [IsLocallyNoetherian Z]
    (f : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ) [SmoothOfRelativeDimension d f]
    (t : Z ⟶ Spec (.of ℂ[X])) [Flat t]
    (A B : IrreducibleCloseds Z) [Flat (CycleClass.Geometric.GenericPoint.reducedSupportι B ≫ t)]
    (x : Z) (hxA : x ∈ (A : Set Z)) (hxB : x ∈ (B : Set Z)) (a : ℂ)
    (hr : Local.Principal.supportStalkMap Z A x hxA (Affine.ParameterFiber.germ ℂ t x a) ≠ 0)
    (S : Type) [CommRing S] [Algebra (Z.presheaf.stalk x) S]
    (hφ : Function.Surjective (algebraMap (Z.presheaf.stalk x) S))
    (hk : RingHom.ker (algebraMap (Z.presheaf.stalk x) S) =
      Ideal.span {Affine.ParameterFiber.germ ℂ t x a})
    (N₀ : ModuleCat S)
    (eN : QuotSMulTop (Affine.ParameterFiber.germ ℂ t x a) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB) ≃ₗ[
      Z.presheaf.stalk x] (ModuleCat.restrictScalars (algebraMap (Z.presheaf.stalk x) S)).obj N₀)
    (s : ℕ) (hBdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B f ≤ s)
    (heq : (Foundations.Scheme.SupportDimension.supportTranscendenceDimension A f - 1) + s =
      d + Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f)
    (hi : Module.support (Z.presheaf.stalk x)
        (QuotSMulTop (Affine.ParameterFiber.germ ℂ t x a) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hxA)) ∩
      Module.support (Z.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB) ⊆
        {IsLocalRing.closedPoint (Z.presheaf.stalk x)}) :
    ∃ F : Finset (PrimeSpectrum (Z.presheaf.stalk x)),
      (∀ p ∈ F, p ∈ Module.support (Z.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hxA) ∧
        Affine.ParameterFiber.germ ℂ t x a ∈ p.asIdeal ∧
        Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure Z x p) f = Foundations.Scheme.SupportDimension.supportTranscendenceDimension A f - 1) ∧
      (∀ p, Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure Z x p) f = Foundations.Scheme.SupportDimension.supportTranscendenceDimension A f - 1 →
        p ∉ F → FiltrationBaseLength.length (Z.presheaf.stalk x) (Localization.AtPrime p.asIdeal)
          (.of _ (QuotSMulTop (Affine.ParameterFiber.germ ℂ t x a) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hxA))) = 0) ∧
      Tor.Euler.euler (Z.presheaf.stalk x)
        (.of _ (QuotSMulTop (Affine.ParameterFiber.germ ℂ t x a) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hxA)))
        (CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB) d =
        ∑ p ∈ F, GlobalParameterSum.Weights.weight Z (Z.fromSpecStalk x p)
          (Affine.ParameterFiber.germ ℂ t (Z.fromSpecStalk x p) a) A *
            Tor.Euler.euler S (.of S (S ⧸ p.asIdeal.map (algebraMap (Z.presheaf.stalk x) S))) N₀ d := by
  let : Smooth f := SmoothOfRelativeDimension.smooth d f
  let R := Z.presheaf.stalk x
  let r := Affine.ParameterFiber.germ ℂ t x a
  let N := CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB
  let : Module.Finite R N := Local.TorFinite.localSupportModule_finite Z B x hxB
  obtain ⟨F, hF, hout, he⟩ := IntrinsicPrincipalDimension.Intrinsic.exists_data f d A x hxA r hr
  refine ⟨F, hF, hout, ?_⟩
  have hN : ∀ p ∈ Module.support R N,
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure Z x p) f ≤ s := by
    intro p hp
    exact ((Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_strictMono f).monotone
      (IntrinsicPrincipalDimension.Intrinsic.support_le Z B x hxB p hp)).trans hBdim
  rw [he N s hN heq hi]
  apply Finset.sum_congr rfl
  intro p hp
  apply congrArg₂ (fun w e : ℚ => w * e)
  · exact IntrinsicParameterLength.Intrinsic.weight Z A t x hxA a p (hF p hp).1 hr
  · exact FiberPrimeTor.euler R S hφ r (ProjectionFormula.Flat.AffineParameter.regular ℂ t x a) hk
      p.asIdeal (hF p hp).2.1 N (ProjectionFormula.Flat.AffineParameter.support_regular Z B t x hxB a) N₀ eN d

end Intrinsic

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntrinsicFiberWeightedEuler
