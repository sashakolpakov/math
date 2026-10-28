import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ScaledMarkedPeriodTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IntegralHodgeMaps
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PeriodMaps

/-! # Scaled Marked Isogenies -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ScaledMarkedIsogenies

noncomputable section

/-! The two cleared marked lattice maps algebraize to original abelian
scheme isogenies, with their exact rational period maps and the square
scalar complement. Inverse Hodge preservation is derived from the
forward Hodge map; no extra denominator is chosen. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

namespace AbelianNativeAdapter

theorem originalIntegralHodgeMap_originalPeriodMap
    {g h : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (B : HilbertConstruction.Abelian.Schemes.AbelianScheme h Foundations.Scheme.ProjectiveSpace.complexBase)
    (PA : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    (PB : Foundations.Scheme.SmoothProjective.ProjectivePresentation B.scheme.left B.scheme.hom)
    (f : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA) →ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB))
    (hf : ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA))
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB)) f)
    (hΛ : ∀ x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA), f x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB)) :
    Reference.PeriodMaps.AbelianIntrinsicAdapter.originalPeriodMap A B PA PB (Reference.IntegralHodgeMaps.AbelianIntrinsicAdapter.originalIntegralHodgeMap A B PA PB f hf hΛ) = f := by
  have h := Reference.IntegralHodgeMaps.AbelianIntrinsicAdapter.originalIntegralHodgeMap_rational A B PA PB f hf hΛ
  simpa only [Reference.PeriodMaps.AbelianIntrinsicAdapter.nativeComparisonMap_eq, Reference.PeriodMaps.AbelianIntrinsicAdapter.originalPeriodMap] using h

end AbelianNativeAdapter

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    {g : ℕ} (A B : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (PA : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    (PB : Foundations.Scheme.SmoothProjective.ProjectivePresentation B.scheme.left B.scheme.hom)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (σ : ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)
    (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)

theorem exists_exact_scaled_marked_isogenies
    (hu : ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA))
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB))
      (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u).toLinearMap)
    (D : ℕ) (hD : 0 < D)
    (m : Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice A PA ρ s hs hg hdegree →ₗ[ℤ] Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice B PB σ s hs hg hdegree)
    (m' : Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice B PB σ s hs hg hdegree →ₗ[ℤ] Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice A PA ρ s hs hg hdegree)
    (hm : ∀ x, (m x).val = D • u x.val)
    (hm' : ∀ x, (m' x).val = D • u.symm x.val) :
    ∃ (f : HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (v : HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A),
      Etale f.hom.left ∧ Etale v.hom.left ∧
      f.hom ≫ v.hom = (𝟙 A.scheme) ^ (D ^ 2) ∧
      v.hom ≫ f.hom = (𝟙 B.scheme) ^ (D ^ 2) ∧
      Reference.PeriodMaps.AbelianIntrinsicAdapter.originalPeriodMap A B PA PB f.hom =
        D • (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u).toLinearMap ∧
      Reference.PeriodMaps.AbelianIntrinsicAdapter.originalPeriodMap B A PB PA v.hom =
        D • (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport B A PB PA σ ρ s hs hg hdegree u.symm).toLinearMap ∧
      (∀ a, ρ.map a ≫ f.hom = f.hom ≫ σ.map a) ∧
      (∀ a, σ.map a ≫ v.hom = v.hom ≫ ρ.map a) := by
  let q := D • (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u).toLinearMap
  let r := D • (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport B A PB PA σ ρ s hs hg hdegree u.symm).toLinearMap
  have hqH : ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA))
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB)) q := ScaledMarkedPeriodTransport.isHodgeMap_nsmul hu D
  have hrH : ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB))
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)) r :=
    ScaledMarkedPeriodTransport.isHodgeMap_nsmul (ScaledMarkedPeriodTransport.NativePELMarking.markedPeriodTransport_reverse_isHodgeMap A B PA PB ρ σ s hs hg hdegree u hu) D
  have hqΛ : ∀ x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA), q x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB) :=
    ScaledMarkedPeriodTransport.NativePELMarking.scaledMarkedPeriodTransport_integral A B PA PB ρ σ s hs hg hdegree u D m hm
  have hrΛ : ∀ x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB), r x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA) :=
    ScaledMarkedPeriodTransport.NativePELMarking.scaledMarkedPeriodTransport_integral B A PB PA σ ρ s hs hg hdegree u.symm D m' hm'
  have hqr : r.comp q = D ^ 2 • (LinearMap.id : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA) →ₗ[ℚ] _) :=
    ScaledMarkedPeriodTransport.NativePELMarking.scaledMarkedPeriodTransport_comp A B PA PB ρ σ s hs hg hdegree u D
  have hrq : q.comp r = D ^ 2 • (LinearMap.id : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB) →ₗ[ℚ] _) := by
    simpa only [LinearEquiv.symm_symm] using
      ScaledMarkedPeriodTransport.NativePELMarking.scaledMarkedPeriodTransport_comp B A PB PA σ ρ s hs hg hdegree u.symm D
  have hn : 0 < D ^ 2 := pow_pos hD _
  let f := Reference.IntegralHodgeMaps.AbelianIntrinsicAdapter.originalIntegralHodgeIsogeny A B PA PB q hqH hqΛ r hrH hrΛ (D ^ 2) hn hqr hrq
  let v := Reference.IntegralHodgeMaps.AbelianIntrinsicAdapter.originalIntegralHodgeIsogeny B A PB PA r hrH hrΛ q hqH hqΛ (D ^ 2) hn hrq hqr
  refine ⟨f, v, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Reference.IntegralHodgeMaps.AbelianIntrinsicAdapter.originalIntegralHodgeMap_finite_etale A B PA PB q hqH hqΛ r hrH hrΛ
      (D ^ 2) hn hqr hrq).2.1
  · exact (Reference.IntegralHodgeMaps.AbelianIntrinsicAdapter.originalIntegralHodgeMap_finite_etale B A PB PA r hrH hrΛ q hqH hqΛ
      (D ^ 2) hn hrq hqr).2.1
  · exact Reference.IntegralHodgeMaps.AbelianIntrinsicAdapter.originalIntegralHodgeMaps_scalar_composition A B PA PB q hqH hqΛ r hrH hrΛ (D ^ 2) hqr
  · exact Reference.IntegralHodgeMaps.AbelianIntrinsicAdapter.originalIntegralHodgeMaps_scalar_composition B A PB PA r hrH hrΛ q hqH hqΛ (D ^ 2) hrq
  · exact AbelianNativeAdapter.originalIntegralHodgeMap_originalPeriodMap A B PA PB q hqH hqΛ
  · exact AbelianNativeAdapter.originalIntegralHodgeMap_originalPeriodMap B A PB PA r hrH hrΛ
  · exact Reference.IntegralHodgeMaps.AbelianIntrinsicAdapter.originalIntegralHodgeMap_intertwines A B PA PB q hqH hqΛ ρ σ
      (ScaledMarkedPeriodTransport.NativePELMarking.scaledMarkedPeriodTransport_integral_action A B PA PB ρ σ s hs hg hdegree u D)
  · exact Reference.IntegralHodgeMaps.AbelianIntrinsicAdapter.originalIntegralHodgeMap_intertwines B A PB PA r hrH hrΛ σ ρ
      (ScaledMarkedPeriodTransport.NativePELMarking.scaledMarkedPeriodTransport_integral_action B A PB PA σ ρ s hs hg hdegree u.symm D)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ScaledMarkedIsogenies
