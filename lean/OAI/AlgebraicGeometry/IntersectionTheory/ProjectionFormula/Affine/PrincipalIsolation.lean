import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.CoverIsolation
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalBaseChange

/-! # Principal Isolation -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalIsolation

noncomputable section

/-! The geometric full-support cover gives isolation for the
actual principal quotient of the reduced-support stalk module. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportStalk

theorem isolated (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m V.structureMap]
    (R : Type) [CommRing R] (j : Spec (.of R) ⟶ V.carrier) [IsOpenImmersion j]
    (v : PrimeSpectrum R) (r : R) (F : Finset (IrreducibleCloseds V.carrier))
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
    (hvx : v.asIdeal ≤ x.asIdeal) :
    Module.support ((Spec (.of R)).presheaf.stalk x)
        (QuotSMulTop (StructureSheaf.toStalk R x r)
          (CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) (SupportStalk.support R v) x (SupportStalk.mem R v x hvx))) ∩
      Module.support ((Spec (.of R)).presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) A₀ x hxA) ⊆
        {IsLocalRing.closedPoint ((Spec (.of R)).presheaf.stalk x)} := by
  let : Algebra R ((Spec (.of R)).presheaf.stalk x) := (StructureSheaf.toStalk R x).hom.toAlgebra
  have h := CoverIsolation.isolated V m p q R j (.of R (QuotSMulTop r (R ⧸ v.asIdeal)))
    F hF hcover A A₀ hA hproper C x hx hxA
  rwa [(PrincipalBaseChange.equiv R v x hvx r).support_eq] at h

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalIsolation
