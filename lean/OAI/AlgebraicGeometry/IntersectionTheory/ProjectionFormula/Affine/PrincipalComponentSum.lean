import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.PrincipalComponentSum
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoveredPrincipalExpansion

/-! # Principal Component Sum -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalComponentSum

noncomputable section

/-! Geometric support covers identify an affine principal quotient
with a sum of native ambient intersection-component weights. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportStalk

theorem coefficient (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m V.structureMap]
    (R : Type) [CommRing R] [IsNoetherianRing R]
    (j : Spec (.of R) ⟶ V.carrier) [IsOpenImmersion j]
    (v : PrimeSpectrum R) (r : R) (hr : r ∉ v.asIdeal)
    (W : IrreducibleCloseds V.carrier) (hW : j v = CycleClass.Thom.IntersectionGeometry.supportPoint W)
    (F : Finset (IrreducibleCloseds V.carrier))
    (hF : ∀ B ∈ F, q ≤ V.supportCodimension B)
    (hcover : ∀ w ∈ Module.support R (QuotSMulTop r (R ⧸ v.asIdeal)),
      ∃ B ∈ F, j w ∈ (B : Set V.carrier))
    (A : V.DimensionCycleSupport p) (A₀ : IrreducibleCloseds (Spec (.of R)))
    (hA : j (CycleClass.Thom.IntersectionGeometry.supportPoint A₀) = CycleClass.Thom.IntersectionGeometry.supportPoint A.val)
    (hproper : ∀ B ∈ F, ∀ D : IrreducibleCloseds V.carrier,
      (D : Set V.carrier) ⊆ (A.val : Set V.carrier) ∩ (B : Set V.carrier) →
        p + V.supportCodimension B ≤ V.supportCodimension D)
    (C : V.DimensionCycleSupport (p + q)) (x : PrimeSpectrum R)
    (hx : j x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val) (hxA : x ∈ (A₀ : Set (Spec (.of R))))
    (hvx : v.asIdeal ≤ x.asIdeal) (s : V.carrier.presheaf.stalk (j x))
    (hs : j.stalkMap x s = StructureSheaf.toStalk R x r) :
    CoveredPrincipalExpansion.pairing R v r A₀ x hxA hvx m =
      ∑ D ∈ Finite.ClosedComponents.components V.carrier
          (IsolatedGeometricComponents.intersection V.carrier W A.val),
        TotalTorCoefficient.coefficient V.carrier W A.val (CycleClass.Thom.IntersectionGeometry.supportPoint D) m *
          GlobalParameterSum.Weights.weight V.carrier (j x) s D := by
  let : IsDomain (V.carrier.presheaf.stalk (j x)) := V.stalk_isDomain (j x)
  have hW₀ : j (CycleClass.Thom.IntersectionGeometry.supportPoint (SupportStalk.support R v)) = CycleClass.Thom.IntersectionGeometry.supportPoint W := by rw [SupportStalk.point]; exact hW
  have hxW₀ := SupportStalk.mem R v x hvx
  have hxW : j x ∈ (W : Set V.carrier) :=
    CoverIsolation.image_subset j (SupportStalk.support R v) W hW₀ ⟨x, hxW₀, rfl⟩
  have hxAj : j x ∈ (A.val : Set V.carrier) :=
    CoverIsolation.image_subset j A₀ A.val hA ⟨x, hxA, rfl⟩
  let : HasProjectiveDimensionLE (CycleClass.Thom.IntersectionGeometry.localSupportModule V.carrier A.val (j x) hxAj) m :=
    Smooth.StalkDimension.stalk_bound V.structureMap m (j x) _
  have hiso := PrincipalIsolation.isolated V m p q R j v r F hF hcover A A₀ hA hproper
    C x hx hxA hvx
  have hnonzero := PrincipalBaseChange.SupportOrder.image_ne_zero R v x hvx r hr
  have he := Open.PrincipalComponentSum.coefficient j (SupportStalk.support R v) A₀ W A.val hW₀ hA x
    hxW₀ hxA hxW hxAj s (by rwa [hs]) m (by rwa [hs])
  unfold CoveredPrincipalExpansion.pairing
  rw [← hs]
  exact he

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalComponentSum
