import OAI.RepresentationTheory.Theta.Geometric.AutomorphicFamilies
import OAI.RepresentationTheory.Theta.Geometric.Finite.AutomorphyTrace

/-! # Automorphic Family Constructors -/

namespace OAI.RepresentationTheory.Theta.Geometric.AutomorphicFamilyConstructors.CM.Torus.AutomorphicTheta

noncomputable section

/-! The ordinary theta coordinates and the odd generators become finite
families of sections for the original automorphy factor. -/

open scoped ContDiff

variable {Φ : Torus.Data.CM.ProjectivePeriodData}
  (H : Φ.space →ₗ⋆[ℂ] Φ.space →ₗ[ℂ] ℂ) (J : Φ.AutomorphyFactor)
  (hsq : ∀ (l : Φ.periodIntegerLattice) z,
    J.value l z ^ 2 = Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.doubledAutomorphy H l.val z)

def evenThetaSection {n : ℕ}
    (t : Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.ThetaSection H Φ.periodIntegerLattice.toAddSubgroup n) : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J (2 * n) where
  toFun := t
  regular := t.regular
  translates l z := by
    rw [pow_mul, hsq]
    exact t.translates l z

def evenThetaFamily (F : Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.FiniteSectionFamily H Φ.periodIntegerLattice.toAddSubgroup) :
    AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J := by
  classical
  exact {
    degree := 2 * F.degree
    sections := F.sections.image (evenThetaSection H J hsq)
    nonzero := fun p => by
      obtain ⟨s, hs, hp⟩ := F.nonzero p
      exact ⟨evenThetaSection H J hsq s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, hp⟩ }

theorem evenThetaFamily_separates
    (F : Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.FiniteSectionFamily H Φ.periodIntegerLattice.toAddSubgroup)
    (p q : Φ.space) (h : F.Separates p q) : (evenThetaFamily H J hsq F).Separates p q := by
  classical
  obtain ⟨s, hs, t, ht, he⟩ := h
  exact ⟨evenThetaSection H J hsq s, Finset.mem_image.mpr ⟨s, hs, rfl⟩,
    evenThetaSection H J hsq t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, he⟩

theorem evenThetaFamily_detects
    (F : Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.FiniteSectionFamily H Φ.periodIntegerLattice.toAddSubgroup)
    (p v : Φ.space) (h : F.Detects p v) : (evenThetaFamily H J hsq F).Detects p v := by
  classical
  obtain ⟨s, hs, t, ht, hp, he⟩ := h
  exact ⟨evenThetaSection H J hsq s, Finset.mem_image.mpr ⟨s, hs, rfl⟩,
    evenThetaSection H J hsq t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, hp, he⟩

theorem evenThetaFamily_injective
    (F : Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.FiniteSectionFamily H Φ.periodIntegerLattice.toAddSubgroup)
    (hF : Function.Injective F.projectiveMap) :
    Function.Injective (evenThetaFamily H J hsq F).projectiveMap := by
  intro p q he
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective p
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective q
  apply hF
  apply (F.projectiveMap_eq_of_not_separates v w).mpr
  intro hs
  exact ((evenThetaFamily H J hsq F).projectiveMap_eq_of_not_separates v w).mp he
    (evenThetaFamily_separates H J hsq F v w hs)

def familyOfFunctions (n : ℕ) (F : Finset (Φ.space → ℂ))
    (hreg : ∀ t ∈ F, ContDiff ℂ ∞ t)
    (htrans : ∀ t ∈ F, ∀ (l : Φ.periodIntegerLattice) z, t (z + l.val) = J.value l z ^ n * t z)
    (hnonzero : ∀ p : Φ.space, ∃ t ∈ F, t p ≠ 0) : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J := by
  classical
  let s (t : F) : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J n := ⟨t.val, (hreg t.val t.property).of_le (by simp), htrans t.val t.property⟩
  exact {
    degree := n
    sections := Finset.univ.image s
    nonzero := fun p => by
      obtain ⟨t, ht, hp⟩ := hnonzero p
      exact ⟨s ⟨t, ht⟩, Finset.mem_image.mpr ⟨⟨t, ht⟩, Finset.mem_univ _, rfl⟩, hp⟩ }

end

end OAI.RepresentationTheory.Theta.Geometric.AutomorphicFamilyConstructors.CM.Torus.AutomorphicTheta
