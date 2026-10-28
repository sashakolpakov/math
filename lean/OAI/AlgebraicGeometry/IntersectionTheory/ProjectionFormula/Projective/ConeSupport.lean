import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearPrimeIdeal
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.FiniteProjective

/-! # Cone Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConeSupport

noncomputable section

/-! The prime homogeneous cone ideal defines an actual irreducible
closed support in ambient projective space, with its native generic point. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {m n : ℕ} (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)
  (hL : LinearIndependent ℂ L) (η : Foundations.Scheme.ProjectiveSpace.projectiveSpace m)

def coordinates : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading n :=
  HomogeneousCoordinateMap.ofForms (fun i => (L i).val) (fun i => (L i).property)

def ideal : HomogeneousIdeal (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) := η.asHomogeneousIdeal.map (coordinates L)

include hL in
theorem prime : (ideal L η).toIdeal.IsPrime :=
  LinearPrimeIdeal.Projection.map_isPrime L hL η.asHomogeneousIdeal.toIdeal

include hL in
theorem not_irrelevant : ¬ HomogeneousIdeal.irrelevant (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) ≤ ideal L η := by
  intro hh
  obtain ⟨i, hi⟩ := Foundations.Scheme.ProjectiveCoordinateCover.exists_mem_projectiveCoordinateOpen m η
  have hf : coordinates L (MvPolynomial.X i) ∈ ideal L η :=
    hh (HomogeneousIdeal.mem_irrelevant_of_mem (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) Nat.zero_lt_one
      ((coordinates L).map_mem (MvPolynomial.isHomogeneous_X ℂ i)))
  have hc : MvPolynomial.X i ∈
      (η.asHomogeneousIdeal.toIdeal.map (coordinates L).toRingHom).comap (coordinates L).toRingHom := hf
  have he := LinearPrimeIdeal.Projection.comap_map L hL η.asHomogeneousIdeal.toIdeal
  exact hi (Eq.mp (congrArg (fun P : Ideal (Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m) => MvPolynomial.X i ∈ P) he) hc)

def genericPoint : Foundations.Scheme.ProjectiveSpace.projectiveSpace n := ⟨ideal L η, prime L hL η, not_irrelevant L hL η⟩

def support : IrreducibleCloseds (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) := irreducibleSetEquivPoints.symm (genericPoint L hL η)

theorem mem_support (x : Foundations.Scheme.ProjectiveSpace.projectiveSpace n) :
    x ∈ support L hL η ↔ ideal L η ≤ x.asHomogeneousIdeal :=
  (ProjectiveSpectrum.le_iff_mem_closure (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (genericPoint L hL η) x).symm

theorem point_in_domain : genericPoint L hL η ∈ BasicOpen.RationalProjection.domain (coordinates L) := by
  obtain ⟨i, hi⟩ := Foundations.Scheme.ProjectiveCoordinateCover.exists_mem_projectiveCoordinateOpen m η
  apply Opens.mem_iSup.mpr
  refine ⟨i, ?_⟩
  change coordinates L (MvPolynomial.X i) ∉ (ideal L η).toIdeal
  intro hf
  have hc : MvPolynomial.X i ∈
      (η.asHomogeneousIdeal.toIdeal.map (coordinates L).toRingHom).comap (coordinates L).toRingHom := hf
  have he := LinearPrimeIdeal.Projection.comap_map L hL η.asHomogeneousIdeal.toIdeal
  exact hi (Eq.mp (congrArg (fun P : Ideal (Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m) => MvPolynomial.X i ∈ P) he) hc)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConeSupport
