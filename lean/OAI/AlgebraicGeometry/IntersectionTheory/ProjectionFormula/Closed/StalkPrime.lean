import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.TotalTorCoefficient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Truncation
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

/-! # Stalk Prime -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.StalkPrime

noncomputable section

/-! A stalk prime containing a closed fiber's kernel is the actual
prime quotient of a reduced support on that fiber. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

variable {Y Z : Scheme} (i : Y ⟶ Z) [IsClosedImmersion i] (x : Y)
  (p : PrimeSpectrum (Z.presheaf.stalk (i x)))
  (hp : RingHom.ker (i.stalkMap x).hom ≤ p.asIdeal)

def prime : PrimeSpectrum (Y.presheaf.stalk x) :=
  ⟨p.asIdeal.map (i.stalkMap x).hom, Ideal.map_isPrime_of_surjective (i.stalkMap_surjective x) hp⟩

theorem comap : PrimeSpectrum.comap (i.stalkMap x).hom (prime i x p hp) = p := by
  apply PrimeSpectrum.ext
  change (p.asIdeal.map (i.stalkMap x).hom).comap (i.stalkMap x).hom = p.asIdeal
  rw [Ideal.comap_map_of_surjective _ (i.stalkMap_surjective x),
    ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hp]

theorem image : i (Y.fromSpecStalk x (prime i x p hp)) = Z.fromSpecStalk (i x) p := by
  have h := congrArg (fun g : Spec (Y.presheaf.stalk x) ⟶ Z => g (prime i x p hp))
    (Scheme.SpecMap_stalkMap_fromSpecStalk (f := i) (x := x))
  change Z.fromSpecStalk (i x) (PrimeSpectrum.comap (i.stalkMap x).hom (prime i x p hp)) = _ at h
  rw [StalkPrime.comap] at h
  exact h.symm

def support : IrreducibleCloseds Y := Stalk.DivisorSupport.primeClosure Y x (prime i x p hp)

theorem support_retraction (q : Z ⟶ Y) (hq : i ≫ q = 𝟙 Y) :
    support i x p hp = irreducibleSetEquivPoints.symm (q (Z.fromSpecStalk (i x) p)) := by
  have hr (y : Y) : q (i y) = y := congrArg (fun h : Y ⟶ Y => h y) hq
  change irreducibleSetEquivPoints.symm (Y.fromSpecStalk x (prime i x p hp)) = _
  rw [← image i x p hp, hr]

theorem point_mem : x ∈ (support i x p hp : Set Y) := Stalk.DivisorSupport.point_mem_primeClosure Y x (prime i x p hp)

def moduleEquiv :
    CycleClass.Thom.IntersectionGeometry.localSupportModule Y (support i x p hp) x (point_mem i x p hp) ≃ₗ[Y.presheaf.stalk x]
      (Y.presheaf.stalk x ⧸ p.asIdeal.map (i.stalkMap x).hom) :=
  Stalk.PrimeQuotient.moduleEquiv Y (support i x p hp) x (point_mem i x p hp)
    (prime i x p hp) (Stalk.DivisorSupport.primeClosure_point Y x (prime i x p hp)).symm

theorem euler (B : IrreducibleCloseds Y) (hxB : x ∈ (B : Set Y)) (d : ℕ) :
    Tor.Euler.euler (Y.presheaf.stalk x)
      (.of _ (Y.presheaf.stalk x ⧸ p.asIdeal.map (i.stalkMap x).hom))
      (CycleClass.Thom.IntersectionGeometry.localSupportModule Y B x hxB) d =
        TotalTorCoefficient.coefficient Y (support i x p hp) B x d := by
  rw [← PrimeFiltrationEuler.euler_iso_left (Y.presheaf.stalk x)
    (moduleEquiv i x p hp).toModuleIso (CycleClass.Thom.IntersectionGeometry.localSupportModule Y B x hxB) d,
    TotalTorCoefficient.coefficient, dite_eq_left ⟨point_mem i x p hp, hxB⟩]
  rfl

theorem projective_coefficient (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (A B C : IrreducibleCloseds X.carrier)
    (d : ℕ) (hd : m ≤ d) :
    TotalTorCoefficient.coefficient X.carrier A B (CycleClass.Thom.IntersectionGeometry.supportPoint C) d =
      CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A B C := by
  classical
  by_cases h : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (A : Set X.carrier) ∧ CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (B : Set X.carrier)
  · rw [TotalTorCoefficient.coefficient, dite_eq_left h]
    exact (Truncation.local_euler_sum_stable X m A B (CycleClass.Thom.IntersectionGeometry.supportPoint C) h.1 h.2 d hd).trans
      (Truncation.intersectionMultiplicity_eq_relative_sum X m A B C h.1 h.2).symm
  · rw [TotalTorCoefficient.coefficient, dite_eq_right h, CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity]
    split_ifs with h'
    · exact False.elim (h h')
    · rfl

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.StalkPrime
