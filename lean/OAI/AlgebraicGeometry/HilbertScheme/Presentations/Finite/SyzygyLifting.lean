import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.SyzygyBound

/-! # Syzygy Lifting -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.SyzygyLifting.GradedHilbert

noncomputable section

/-! Lifting relations in a bounded range of homogeneous degrees suffices to lift every relation after a surjective coefficient specialization. -/

open _root_.MvPolynomial

universe u v z

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]
variable {n : ℕ} {ι : Type z} [Fintype ι]

def mapRelationVector (φ : R →+* S) (a : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing S n :=
  fun i => MvPolynomial.map φ (a i)

theorem map_polynomialRelationMap (φ : R →+* S) (g a : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) :
    MvPolynomial.map φ (SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap g a) =
      SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap (mapRelationVector φ g) (mapRelationVector φ a) := by
  simp [SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap, mapRelationVector, map_sum, map_mul]

def liftedPolynomialRelations (φ : R →+* S) (hφ : Function.Surjective φ)
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) : Submodule (Hilbert.Polynomial.GradedHilbert.CoordinateRing S n) (ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing S n) where
  carrier := {a | ∃ b, SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap g b = 0 ∧ mapRelationVector φ b = a}
  zero_mem' := ⟨0, map_zero _, by funext i; simp [mapRelationVector]⟩
  add_mem' := by
    rintro a b ⟨a', ha', rfl⟩ ⟨b', hb', rfl⟩
    refine ⟨a' + b', by rw [map_add, ha', hb', add_zero], ?_⟩
    funext i
    simp [mapRelationVector]
  smul_mem' := by
    rintro c a ⟨b, hb, rfl⟩
    obtain ⟨c', hc'⟩ := MvPolynomial.map_surjective φ hφ c
    refine ⟨c' • b, by rw [map_smul, hb, smul_zero], ?_⟩
    funext i
    simp only [mapRelationVector, Pi.smul_apply, smul_eq_mul, map_mul, hc']

theorem liftedPolynomialRelations_le_kernel (φ : R →+* S) (hφ : Function.Surjective φ)
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) :
    liftedPolynomialRelations φ hφ g ≤ LinearMap.ker (SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap (mapRelationVector φ g)) := by
  rintro a ⟨b, hb, rfl⟩
  change SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap (mapRelationVector φ g) (mapRelationVector φ b) = 0
  rw [← map_polynomialRelationMap, hb, map_zero]

theorem all_relations_lift_of_bounded_homogeneous_lifts
    {K : Type v} [Field K] (φ : R →+* K) (hφ : Function.Surjective φ)
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)
    (hlift : ∀ d ≤ Coordinate.SyzygyBound.GradedHilbert.homogeneousSyzygyDegreeBound n (Fintype.card ι) N,
      ∀ a : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n, (∀ i, (a i).IsHomogeneous d) →
        SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap (mapRelationVector φ g) a = 0 →
          ∃ b : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n, SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap g b = 0 ∧ mapRelationVector φ b = a) :
    liftedPolynomialRelations φ hφ g = LinearMap.ker (SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap (mapRelationVector φ g)) := by
  have hgK (i : ι) : (mapRelationVector φ g i).IsHomogeneous N := (hg i).map φ
  obtain ⟨B, hB, hdeg⟩ := Coordinate.SyzygyBound.GradedHilbert.exists_uniform_coordinate_syzygy_generators (mapRelationVector φ g) N hgK
  apply le_antisymm (liftedPolynomialRelations_le_kernel φ hφ g)
  rw [hB]
  apply Submodule.span_le.mpr
  intro a ha
  obtain ⟨d, hd, hhom⟩ := hdeg a ha
  apply hlift d hd a hhom
  apply LinearMap.mem_ker.mp
  rw [hB]
  exact Submodule.subset_span ha

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.SyzygyLifting.GradedHilbert
