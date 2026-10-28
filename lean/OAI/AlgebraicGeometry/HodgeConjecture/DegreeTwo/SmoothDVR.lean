import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothNormal
import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.KrullDimension.Field

/-! # Smooth DVR -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothDVR.Constructions

noncomputable section

/-!
# DegreeTwo: codimension-one local rings of smooth varieties are DVRs

Normality is derived from smoothness. The actual stalk has Krull dimension
equal to its point's coheight, so at codimension one the Noetherian normal
local-domain criterion proves the discrete valuation ring property.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

universe u v w

theorem isIntegrallyClosed_of_isLocalizationAtPrime_of_smooth
    (K : Type u) (S : Type v) (A : Type w)
    [Field K] [CommRing S] [Algebra K S] [Algebra.Smooth K S]
    [CommRing A] [Algebra S A] (p : Ideal S) [p.IsPrime]
    [IsLocalization.AtPrime A p] : IsIntegrallyClosed A := by
  let : IsIntegrallyClosed (Localization.AtPrime p) :=
    SmoothNormal.Constructions.isIntegrallyClosed_localizationAtPrime_of_isSmoothAt K S p
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) A).toRingEquiv

/-- The actual stalks, with their original ring structure, are integrally closed. -/
theorem smoothScheme_stalk_isIntegrallyClosed {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := Foundations.Scheme.AffineOpenSmooth.specSectionScalarAlgebra_smooth f U hU
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let := hU.isLocalization_stalk ⟨x, hxU⟩
  let p := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  exact isIntegrallyClosed_of_isLocalizationAtPrime_of_smooth K Γ(X, U) (X.presheaf.stalk x) p

/-- Smooth codimension-one stalks are discrete valuation rings, with no DVR
or regularity assumption added to the input. -/
theorem smoothScheme_stalk_isDiscreteValuationRing {K : Type u} [Field K]
    {X : Scheme.{u}} [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [Smooth f] (x : X) (hx : coheight x = 1) :
    letI := Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_stalk_isDomain f x
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  let : IsDomain (X.presheaf.stalk x) := Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_stalk_isDomain f x
  let : IsIntegrallyClosed (X.presheaf.stalk x) := smoothScheme_stalk_isIntegrallyClosed f x
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  let : Ring.DimensionLEOne (X.presheaf.stalk x) :=
    ⟨fun _ hp => hp.isMaximal_of_ne_bot ‹_›⟩
  let : IsDedekindDomain (X.presheaf.stalk x) := {}
  have hnf : ¬ IsField (X.presheaf.stalk x) := by
    intro h
    have he := ringKrullDim_stalk_eq_coheight x
    rw [ringKrullDim_eq_zero_of_isField h, hx] at he
    exact zero_ne_one he
  exact ((IsDiscreteValuationRing.TFAE (X.presheaf.stalk x) hnf).out 3 1).mp
    (show IsDedekindDomain (X.presheaf.stalk x) from inferInstance)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothDVR.Constructions
