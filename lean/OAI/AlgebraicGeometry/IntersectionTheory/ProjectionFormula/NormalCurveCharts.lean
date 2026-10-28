import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveLocalRings
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-! # Normal Curve Charts -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalCurveCharts

noncomputable section

/-! The coordinate ring of a nonempty affine chart of a normal integral
curve is a Dedekind domain. Normality is expressed in the actual stalk rings. -/

set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem sections_integrallyClosed {X : Scheme} [IsIntegral X]
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) : IsIntegrallyClosed Γ(X, U) := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ hp
  let q : Spec Γ(X, U) := ⟨p, hp.isPrime⟩
  let : IsIntegrallyClosed (X.presheaf.stalk (hU.fromSpec q)) := hNormal _
  let : IsIntegrallyClosed ((Spec Γ(X, U)).presheaf.stalk q) :=
    IsIntegrallyClosed.of_equiv (asIso (hU.fromSpec.stalkMap q)).commRingCatIsoToRingEquiv
  exact IsIntegrallyClosed.of_equiv (Spec.stalkIso Γ(X, U) q).commRingCatIsoToRingEquiv

theorem sections_dedekind {k : Type} [Field k] {X : Scheme} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (hdim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f ≤ 1)
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) : IsDedekindDomain Γ(X, U) := by
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := Foundations.Scheme.AffineSectionFiniteType.specSectionScalarAlgebra_finiteType f U hU
  let : IsNoetherianRing Γ(X, U) := Algebra.FiniteType.isNoetherianRing k Γ(X, U)
  let : IsIntegrallyClosed Γ(X, U) := sections_integrallyClosed hNormal U hU
  let : Ring.KrullDimLE 1 Γ(X, U) := ⟨by
    change ringKrullDim Γ(X, U) ≤ 1
    rw [DivisorClass.Chern.FiniteTypeDimension.Construction.finiteType_ringKrullDim_eq_trdeg k Γ(X, U),
      ← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_affineSections f U hU]
    exact_mod_cast hdim⟩
  let : Ring.DimensionLEOne Γ(X, U) := ⟨fun hn hp => hp.isMaximal_of_ne_bot hn⟩
  exact
    { toIsDomain := inferInstance
      toIsDedekindRing :=
        { toIsNoetherian := inferInstance
          toDimensionLEOne := inferInstance
          toIsIntegralClosure := inferInstance } }

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalCurveCharts
