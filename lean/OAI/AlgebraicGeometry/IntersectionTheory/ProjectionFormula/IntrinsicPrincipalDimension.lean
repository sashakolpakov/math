import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricWeightedEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricSupportLocalization

/-! # Intrinsic Principal Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntrinsicPrincipalDimension

noncomputable section

/-! A nonzero principal parameter on an integral support lowers the
geometric dimension of every prime in its native quotient module. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Intrinsic

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient

theorem support_le (X : Scheme) (A : IrreducibleCloseds X) (x : X) (hx : x ∈ (A : Set X))
    (p : PrimeSpectrum (X.presheaf.stalk x))
    (hp : p ∈ Module.support (X.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule X A x hx)) :
    Stalk.DivisorSupport.primeClosure X x p ≤ A :=
  closure_minimal (Set.singleton_subset_iff.mpr
    (Local.SupportSpectrum.image_mem_support X A x hx p hp)) A.isClosed

theorem support_bound {K : Type} [Field K] {X : Scheme} [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (A : IrreducibleCloseds X) (x : X) (hx : x ∈ (A : Set X))
    (r : X.presheaf.stalk x) (hr : Local.Principal.supportStalkMap X A x hx r ≠ 0)
    (p : PrimeSpectrum (X.presheaf.stalk x))
    (hp : p ∈ Module.support (X.presheaf.stalk x) (QuotSMulTop r (CycleClass.Thom.IntersectionGeometry.localSupportModule X A x hx))) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure X x p) f ≤ Foundations.Scheme.SupportDimension.supportTranscendenceDimension A f - 1 := by
  let := Local.TorFinite.localSupportModule_finite X A x hx
  simp only [Module.support_quotSMulTop, Set.mem_inter_iff, PrimeSpectrum.mem_zeroLocus,
    Set.singleton_subset_iff] at hp
  have hle := support_le X A x hx p hp.1
  have hne : Stalk.DivisorSupport.primeClosure X x p ≠ A := by
    intro he
    have hpoint : X.fromSpecStalk x p = CycleClass.Thom.IntersectionGeometry.supportPoint A :=
      (Stalk.DivisorSupport.primeClosure_point X x p).symm.trans (congrArg CycleClass.Thom.IntersectionGeometry.supportPoint he)
    have hk := Stalk.PrimeQuotient.kernel_eq X A x hx p hpoint
    apply hr
    apply RingHom.mem_ker.mp
    rw [hk]
    exact hp.2
  have hlt := Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_strictMono f (lt_of_le_of_ne hle hne)
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure X x p) f < Foundations.Scheme.SupportDimension.supportTranscendenceDimension A f at hlt
  omega

theorem exists_data {K : Type} [Field K] {X : Scheme} [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) (d : ℕ) [SmoothOfRelativeDimension d f]
    (A : IrreducibleCloseds X) (x : X) (hx : x ∈ (A : Set X))
    (r : X.presheaf.stalk x) (hr : Local.Principal.supportStalkMap X A x hx r ≠ 0) :
    ∃ F : Finset (PrimeSpectrum (X.presheaf.stalk x)),
      (∀ p ∈ F, p ∈ Module.support (X.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule X A x hx) ∧
        r ∈ p.asIdeal ∧
        Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure X x p) f = Foundations.Scheme.SupportDimension.supportTranscendenceDimension A f - 1) ∧
      (∀ p, Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure X x p) f = Foundations.Scheme.SupportDimension.supportTranscendenceDimension A f - 1 →
        p ∉ F → FiltrationBaseLength.length (X.presheaf.stalk x) (Localization.AtPrime p.asIdeal)
          (.of _ (QuotSMulTop r (CycleClass.Thom.IntersectionGeometry.localSupportModule X A x hx))) = 0) ∧
      ∀ (N : ModuleCat (X.presheaf.stalk x)) [Module.Finite (X.presheaf.stalk x) N] (s : ℕ)
        (_hN : ∀ p ∈ Module.support (X.presheaf.stalk x) N,
          Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure X x p) f ≤ s)
        (_heq : (Foundations.Scheme.SupportDimension.supportTranscendenceDimension A f - 1) + s =
          d + Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f)
        (_hi : Module.support (X.presheaf.stalk x) (QuotSMulTop r (CycleClass.Thom.IntersectionGeometry.localSupportModule X A x hx)) ∩
          Module.support (X.presheaf.stalk x) N ⊆ {IsLocalRing.closedPoint (X.presheaf.stalk x)}),
        Tor.Euler.euler (X.presheaf.stalk x) (.of _ (QuotSMulTop r (CycleClass.Thom.IntersectionGeometry.localSupportModule X A x hx))) N d =
          ∑ p ∈ F, ((FiltrationBaseLength.length (X.presheaf.stalk x) (Localization.AtPrime p.asIdeal)
              (.of _ (QuotSMulTop r (CycleClass.Thom.IntersectionGeometry.localSupportModule X A x hx)))).toNat : ℚ) *
            Tor.Euler.euler (X.presheaf.stalk x) (.of _ (X.presheaf.stalk x ⧸ p.asIdeal)) N d := by
  let : Smooth f := SmoothOfRelativeDimension.smooth d f
  let := Local.TorFinite.localSupportModule_finite X A x hx
  obtain ⟨F, hF, hout, he⟩ := GeometricWeightedEuler.exists_data f d x
    (.of _ (QuotSMulTop r (CycleClass.Thom.IntersectionGeometry.localSupportModule X A x hx)))
    (Foundations.Scheme.SupportDimension.supportTranscendenceDimension A f - 1) (support_bound f A x hx r hr)
  refine ⟨F, ?_, hout, ?_⟩
  · intro p hp
    have h := (hF p hp).1
    change p ∈ Module.support (X.presheaf.stalk x) (QuotSMulTop r (CycleClass.Thom.IntersectionGeometry.localSupportModule X A x hx)) at h
    simp only [Module.support_quotSMulTop, Set.mem_inter_iff, PrimeSpectrum.mem_zeroLocus,
      Set.singleton_subset_iff] at h
    exact ⟨h.1, h.2, (hF p hp).2.1⟩
  · intro N _ s hN heq hi
    let : HasProjectiveDimensionLE N d := ProjectionFormula.Smooth.StalkDimension.stalk_bound f d x N
    exact he N s hN heq hi

end Intrinsic

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntrinsicPrincipalDimension
