import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalBaseChange
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.CoverIsolation
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportTor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Truncation
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizedFixedFiltration
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FiltrationAvoidance

/-! # Prime -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.Prime

noncomputable section

/-! Every prime factor in an affine Euler expansion gives exactly
ThomClass's native global intersection coefficient, including factors whose
support misses the chosen point. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem mem_iff {R : Type} [CommRing R] {X : Scheme}
    (j : Spec (.of R) ⟶ X) [IsOpenImmersion j] (w x : PrimeSpectrum R) :
    j x ∈ (FiltrationAvoidance.support j w : Set X) ↔ w.asIdeal ≤ x.asIdeal := by
  change j x ∈ closure ({j w} : Set X) ↔ _
  rw [← specializes_iff_mem_closure]
  exact j.isOpenEmbedding.isInducing.specializes_iff.trans
    (PrimeSpectrum.le_iff_specializes w x).symm

theorem euler (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m V.structureMap]
    (R : Type) [CommRing R] (j : Spec (.of R) ⟶ V.carrier) [IsOpenImmersion j]
    (w : PrimeSpectrum R) (A₀ : IrreducibleCloseds (Spec (.of R)))
    (A C : IrreducibleCloseds V.carrier) (hA : j (CycleClass.Thom.IntersectionGeometry.supportPoint A₀) = CycleClass.Thom.IntersectionGeometry.supportPoint A)
    (x : PrimeSpectrum R) (hx : j x = CycleClass.Thom.IntersectionGeometry.supportPoint C) (hxA : x ∈ (A₀ : Set (Spec (.of R)))) :
    letI : Algebra R ((Spec (.of R)).presheaf.stalk x) := (StructureSheaf.toStalk R x).hom.toAlgebra
    Tor.Euler.euler ((Spec (.of R)).presheaf.stalk x)
      ((Flat.Extension.baseChange R ((Spec (.of R)).presheaf.stalk x)).obj (.of R (R ⧸ w.asIdeal)))
      (CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) A₀ x hxA) m =
      CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity V (FiltrationAvoidance.support j w) A C := by
  let S := (Spec (.of R)).presheaf.stalk x
  let : Algebra R S := (StructureSheaf.toStalk R x).hom.toAlgebra
  let B := FiltrationAvoidance.support j w
  have hxAj : j x ∈ (A : Set V.carrier) :=
    CoverIsolation.image_subset j A₀ A hA ⟨x, hxA, rfl⟩
  have hxAC : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (A : Set V.carrier) := hx ▸ hxAj
  by_cases hw : w.asIdeal ≤ x.asIdeal
  · have hxBj : j x ∈ (B : Set V.carrier) := (mem_iff j w x).mpr hw
    have hxBC : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (B : Set V.carrier) := hx ▸ hxBj
    let B₀ := SupportStalk.support R w
    have hxB₀ := SupportStalk.mem R w x hw
    have hB : j (CycleClass.Thom.IntersectionGeometry.supportPoint B₀) = CycleClass.Thom.IntersectionGeometry.supportPoint B := by
      rw [SupportStalk.point]
      exact (irreducibleSetEquivPoints.apply_symm_apply (j w)).symm
    rw [PrimeFiltrationEuler.euler_iso_left S
      (PrincipalBaseChange.SupportOrder.baseEquiv R w x hw).toModuleIso
        (CycleClass.Thom.IntersectionGeometry.localSupportModule (Spec (.of R)) A₀ x hxA) m,
      Truncation.intersectionMultiplicity_eq_relative_sum V m B A C hxBC hxAC]
    apply Finset.sum_congr rfl
    intro n _
    apply congrArg (fun l : ℕ∞ => (-1 : ℚ) ^ n * (l.toNat : ℚ))
    exact (Open.SupportTor.localTorLength_eq j B₀ A₀ B A hB hA x hxB₀ hxA hxBj hxAj n).trans
      (Open.SupportTor.localTorLength_congr_point V.carrier B A hx hxBj hxAj hxBC hxAC n)
  · let : IsLocalization x.asIdeal.primeCompl S := by
      change IsLocalization x.asIdeal.primeCompl ((structurePresheafInCommRingCat R).stalk x)
      infer_instance
    rw [LocalizedFixedFiltration.prime_euler_zero R S x w hw]
    symm
    apply dite_eq_right
    intro h
    apply hw
    apply (mem_iff j w x).mp
    exact hx.symm ▸ h.1

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.Prime
