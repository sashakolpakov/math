import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.Prime
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SimultaneousAffineEuler

/-! # Intrinsic Affine Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntrinsicAffineEuler

noncomputable section

/-! A properly positioned affine module expansion is a sum of
actual ThomClass intersection multiplicities. Native local Tor finiteness
and the projective-dimension bound follow from the geometry. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Intrinsic

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FiltrationAvoidance

theorem coefficient (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m V.structureMap]
    (R : Type) [CommRing R] [IsNoetherianRing R]
    (j : Spec (.of R) ⟶ V.carrier) [IsOpenImmersion j]
    (M : ModuleCat R) [Module.Finite R M] (F : Finset (PrimeSpectrum R))
    (Z : Finset (IrreducibleCloseds V.carrier))
    (hZ : ∀ B ∈ Z, q ≤ V.supportCodimension B)
    (hcover : ∀ w ∈ Module.support R M, ∃ B ∈ Z, j w ∈ (B : Set V.carrier))
    (a : V.RationalDimensionCycle p)
    (ha : a ∈ Proper.SupportCycles.submodule V p (fun B : Z => B.val))
    (he : SimultaneousAffineEuler.Expansion V p q j M F a)
    (A : V.DimensionCycleSupport p) (hAa : A ∈ a.support)
    (A₀ : IrreducibleCloseds (Spec (.of R))) (hA : j (CycleClass.Thom.IntersectionGeometry.supportPoint A₀) = CycleClass.Thom.IntersectionGeometry.supportPoint A.val)
    (C : V.DimensionCycleSupport (p + q)) (x : PrimeSpectrum R)
    (hx : j x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val) (hxA : x ∈ (A₀ : Set (Spec (.of R)))) :
    letI : Algebra R ((Spec (.of R)).presheaf.stalk x) := (StructureSheaf.toStalk R x).hom.toAlgebra
    Tor.Euler.euler ((Spec (.of R)).presheaf.stalk x)
      ((Flat.Extension.baseChange R ((Spec (.of R)).presheaf.stalk x)).obj M)
      (CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) A₀ x hxA) m =
      ∑ z ∈ F, ((FiltrationBaseLength.length R (Localization.AtPrime z.asIdeal) M).toNat : ℚ) *
        CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity V (Affine.FiltrationAvoidance.support j z) A.val C.val := by
  let S := (Spec (.of R)).presheaf.stalk x
  let : Algebra R S := (StructureSheaf.toStalk R x).hom.toAlgebra
  let N := CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) A₀ x hxA
  let : Module.Finite S N := Local.TorFinite.localSupportModule_finite (Spec (.of R)) A₀ x hxA
  let : HasProjectiveDimensionLE N m :=
    Polynomial.DimensionBound.bound_of_ringEquiv (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv m
      (Smooth.StalkDimension.stalk_bound V.structureMap m (j x)) N
  have hiso := Affine.CoverIsolation.isolated V m p q R j M Z hZ hcover A A₀ hA
    (fun B hB => ha ⟨B, hB⟩ A hAa) C x hx hxA
  have hAC : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set V.carrier) := hx ▸
    Affine.CoverIsolation.image_subset j A₀ A.val hA ⟨x, hxA, rfl⟩
  rw [he A hAa C x hx hAC N m hiso]
  apply Finset.sum_congr rfl
  intro z _
  rw [Affine.Prime.euler V m R j z A₀ A.val C.val hA x hx hxA]

end Intrinsic

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntrinsicAffineEuler
