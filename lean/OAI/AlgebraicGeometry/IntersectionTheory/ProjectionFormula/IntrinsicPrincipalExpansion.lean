import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.AffineExpansion
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntrinsicAffineEuler

/-! # Intrinsic Principal Expansion -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntrinsicPrincipalExpansion

noncomputable section

/-! A positioned principal quotient has the native ThomClass prime
intersection expansion. The stalk resolution bound follows from the
actual smooth chart isomorphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Intrinsic

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportStalk

theorem coefficient (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m V.structureMap]
    (R : Type) [CommRing R] [IsNoetherianRing R]
    (j : Spec (.of R) ⟶ V.carrier) [IsOpenImmersion j]
    (v : PrimeSpectrum R) (r : R) (F : Finset (PrimeSpectrum R)) (a : V.RationalDimensionCycle p)
    (he : Principal.AffineExpansion.Expansion V p q j v r F a)
    (A : V.DimensionCycleSupport p) (hAa : A ∈ a.support)
    (A₀ : IrreducibleCloseds (Spec (.of R))) (hA : j (CycleClass.Thom.IntersectionGeometry.supportPoint A₀) = CycleClass.Thom.IntersectionGeometry.supportPoint A.val)
    (C : V.DimensionCycleSupport (p + q)) (x : PrimeSpectrum R)
    (hx : j x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val) (hxA : x ∈ (A₀ : Set (Spec (.of R))))
    (hvx : v.asIdeal ≤ x.asIdeal)
    (hiso : Module.support ((Spec (.of R)).presheaf.stalk x)
        (QuotSMulTop (StructureSheaf.toStalk R x r)
          (CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) (Affine.SupportStalk.support R v) x (Affine.SupportStalk.mem R v x hvx))) ∩
      Module.support ((Spec (.of R)).presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) A₀ x hxA) ⊆
        {IsLocalRing.closedPoint ((Spec (.of R)).presheaf.stalk x)}) :
    Tor.Euler.euler ((Spec (.of R)).presheaf.stalk x)
      (.of _ (QuotSMulTop (StructureSheaf.toStalk R x r)
        (CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) (Affine.SupportStalk.support R v) x (Affine.SupportStalk.mem R v x hvx))))
      (CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) A₀ x hxA) m =
      ∑ z ∈ F, Affine.PrincipalWeight.weight R v r z *
        CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity V (Affine.FiltrationAvoidance.support j z) A.val C.val := by
  let S := (Spec (.of R)).presheaf.stalk x
  let : Algebra R S := (StructureSheaf.toStalk R x).hom.toAlgebra
  let N := CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) A₀ x hxA
  let : Module.Finite S N := Local.TorFinite.localSupportModule_finite (Spec (.of R)) A₀ x hxA
  let : HasProjectiveDimensionLE N m :=
    Polynomial.DimensionBound.bound_of_ringEquiv (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv m
      (Smooth.StalkDimension.stalk_bound V.structureMap m (j x)) N
  have hAC : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set V.carrier) := hx ▸
    Affine.CoverIsolation.image_subset j A₀ A.val hA ⟨x, hxA, rfl⟩
  rw [he A hAa C x hx hAC hvx N m hiso]
  apply Finset.sum_congr rfl
  intro z _
  rw [Affine.Prime.euler V m R j z A₀ A.val C.val hA x hx hxA]

end Intrinsic

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntrinsicPrincipalExpansion
