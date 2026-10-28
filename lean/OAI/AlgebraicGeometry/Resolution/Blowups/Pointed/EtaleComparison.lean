import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ComparisonFiberProduct

/-! # Etale Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.EtaleComparison.Construction

noncomputable section

/-! A pointed common étale refinement of two coordinate presentations of one ring. -/

open scoped TensorProduct

universe u

variable {k P R S C : Type u} [CommRing k] [CommRing P] [CommRing R] [CommRing S]
  [CommRing C] [Algebra k P] [Algebra k R] [Algebra k S] [Algebra k C]
  [Algebra P R] [Algebra P S] [IsScalarTower k P R] [IsScalarTower k P S]
  [Algebra.Etale P R] [Algebra.Etale P S]

/-- The tensor-product construction gives two actual étale maps from the
original ring and a common point. The isomorphism of the chart rings need only
respect the coefficient ring, so their coordinate presentations can differ. -/
theorem exists_pointed_etale_comparison (e : R ≃ₐ[k] S) (r : R →ₐ[k] C)
    (h : ∀ p : P, r (algebraMap P R p) = r (e.symm (algebraMap P S p))) :
    ∃ f g : R →ₐ[k] R ⊗[P] S, ∃ v : R ⊗[P] S →ₐ[k] C,
      f.toRingHom.Etale ∧ g.toRingHom.Etale ∧
      (∀ p : P, f (algebraMap P R p) = g (e.symm (algebraMap P S p))) ∧
      (∀ x : R, v (f x) = r x) ∧ (∀ x : R, v (g x) = r x) := by
  let f := Blowups.Etale.ComparisonFiberProduct.Construction.etaleComparisonLeft (k := k) (P := P) (R := R) (S := S)
  let g := (Blowups.Etale.ComparisonFiberProduct.Construction.etaleComparisonRight (k := k) (P := P) (R := R) (S := S)).comp e.toAlgHom
  let v := Blowups.Etale.ComparisonFiberProduct.Construction.etaleComparisonPoint r (r.comp e.symm.toAlgHom) h
  refine ⟨f, g, v, Blowups.Etale.ComparisonFiberProduct.Construction.etaleComparisonLeft_etale, ?_, ?_, ?_, ?_⟩
  · have hg : g.toRingHom =
        (Blowups.Etale.ComparisonFiberProduct.Construction.etaleComparisonRight (k := k) (P := P) (R := R) (S := S)).toRingHom.comp
          e.toRingHom := by
      ext x
      rfl
    rw [hg]
    exact RingHom.Etale.stableUnderComposition e.toRingHom
      (Blowups.Etale.ComparisonFiberProduct.Construction.etaleComparisonRight (k := k) (P := P) (R := R) (S := S)).toRingHom
      (RingHom.Etale.of_bijective e.bijective) Blowups.Etale.ComparisonFiberProduct.Construction.etaleComparisonRight_etale
  · intro p
    change Blowups.Etale.ComparisonFiberProduct.Construction.etaleComparisonLeft (k := k) (P := P) (S := S) (algebraMap P R p) =
      Blowups.Etale.ComparisonFiberProduct.Construction.etaleComparisonRight (k := k) (P := P) (R := R) (e (e.symm (algebraMap P S p)))
    rw [e.apply_symm_apply]
    exact Blowups.Etale.ComparisonFiberProduct.Construction.etaleComparison_coordinate_relation p
  · intro x
    exact Blowups.Etale.ComparisonFiberProduct.Construction.etaleComparisonPoint_left r (r.comp e.symm.toAlgHom) h x
  · intro x
    change v (Blowups.Etale.ComparisonFiberProduct.Construction.etaleComparisonRight (k := k) (P := P) (R := R) (e x)) = r x
    calc
      _ = (r.comp e.symm.toAlgHom) (e x) :=
        Blowups.Etale.ComparisonFiberProduct.Construction.etaleComparisonPoint_right r (r.comp e.symm.toAlgHom) h (e x)
      _ = r x := by
        change r (e.symm (e x)) = r x
        rw [e.symm_apply_apply]

/-- A common point valued in a domain supplies an actual prime on the common
chart at which the two maps agree on every original section. -/
theorem exists_prime_pointed_etale_comparison [IsDomain C]
    (e : R ≃ₐ[k] S) (r : R →ₐ[k] C)
    (h : ∀ p : P, r (algebraMap P R p) = r (e.symm (algebraMap P S p))) :
    ∃ f g : R →ₐ[k] R ⊗[P] S, ∃ q : Ideal (R ⊗[P] S),
      q.IsPrime ∧ f.toRingHom.Etale ∧ g.toRingHom.Etale ∧
      (∀ p : P, f (algebraMap P R p) = g (e.symm (algebraMap P S p))) ∧
      (∀ x : R, g x - f x ∈ q) := by
  obtain ⟨f, g, v, hf, hg, hcoords, hvf, hvg⟩ := exists_pointed_etale_comparison e r h
  refine ⟨f, g, RingHom.ker v.toRingHom, ?_, hf, hg, hcoords, ?_⟩
  · exact Ideal.comap_isPrime v.toRingHom ⊥
  · intro x
    change v (g x - f x) = 0
    rw [map_sub, hvf, hvg, sub_self]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.EtaleComparison.Construction
