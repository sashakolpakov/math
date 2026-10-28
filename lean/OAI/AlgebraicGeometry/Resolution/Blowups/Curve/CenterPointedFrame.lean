import OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CenterLocalFrame

/-! # Center Pointed Frame -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CenterPointedFrame.Construction

noncomputable section

/-! Every point of an intrinsic smooth-curve center has an actual open coordinate neighborhood. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

section Derivative

variable (k : Type u) {R : Type u} [CommRing k] [CommRing R] [Algebra k R]

theorem exists_derivative_outside_center_prime
    (I q : Ideal R) [q.IsPrime] (hIq : I ≤ q)
    (hI : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k I = ⊤) :
    ∃ (D : Derivation k R R) (z : I), D z.val ∉ q := by
  by_contra! h
  have hle : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k I ≤ q := by
    apply sup_le hIq
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨D, z⟩, rfl⟩
    exact h D z
  rw [hI] at hle
  exact (inferInstance : q.IsPrime).ne_top (top_le_iff.mp hle)

end Derivative

variable (k : Type u) {R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
  [Algebra k R] [Algebra.Smooth k R] [Algebra ℚ R] [IsNoetherianRing R]

/-- At every prime in a curve center with unit first differential ideal,
an actual affine open immersion preserves that point and turns the original
center into a principal ideal with a dual relative derivation. -/
theorem curve_center_pointed_coordinate_neighborhood
    (hd : ringKrullDim R ≤ 1) (I q : Ideal R) [q.IsPrime]
    (hIq : I ≤ q) (hI : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k I = ⊤) :
    ∃ (S : CommRingCat.{u}) (_ : Algebra k S) (φ : R →ₐ[k] S) (Q : Ideal S),
      Q.IsPrime ∧ Q.comap φ.toRingHom = q ∧
      IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) ∧ Algebra.Smooth k S ∧
      ∃ (g : S) (E : Derivation k S S), I.map φ.toRingHom = Ideal.span {g} ∧ E g = 1 := by
  obtain ⟨D, z, hz⟩ := exists_derivative_outside_center_prime k I q hIq hI
  let A := DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z.val
  let qA := q.map (algebraMap R A)
  have hdis : Disjoint (Submonoid.powers (D z.val) : Set R) q :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime (D z.val)).mpr hz
  let : qA.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers (D z.val)) A q inferInstance hdis
  have hqA : qA.comap (algebraMap R A) = q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers (D z.val)) A inferInstance hdis
  obtain ⟨r, hr, _, hgen, E, hE⟩ := CenterLocalFrame.Construction.curve_center_derivative_local_frame k hd I D z
  have hrq : r ∈ qA := Ideal.map_mono hIq hr
  have hcomp : 1 - r ∉ qA := by
    intro h
    have hone := qA.add_mem h hrq
    rw [sub_add_cancel] at hone
    exact (inferInstance : qA.IsPrime).ne_top (Ideal.eq_top_of_isUnit_mem _ hone isUnit_one)
  let S := Localization.Away (1 - r)
  let Q := qA.map (algebraMap A S)
  have hdis' : Disjoint (Submonoid.powers (1 - r) : Set A) qA :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime (1 - r)).mpr hcomp
  have hQ : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers (1 - r)) S qA inferInstance hdis'
  have hQA : Q.comap (algebraMap A S) = qA :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers (1 - r)) S inferInstance hdis'
  let φ : R →ₐ[k] S := (IsScalarTower.toAlgHom k A S).comp (IsScalarTower.toAlgHom k R A)
  let : Algebra.Smooth R A := Algebra.Smooth.of_isLocalization_Away (D z.val)
  let : Algebra.Smooth k A := Algebra.Smooth.comp k R A
  let : Algebra.Smooth A S := Algebra.Smooth.of_isLocalization_Away (1 - r)
  let : Algebra.Smooth k S := Algebra.Smooth.comp k A S
  refine ⟨.of S, inferInstance, φ, Q, hQ, ?_, ?_, inferInstance,
    algebraMap A S (algebraMap R A z.val), E, ?_, hE⟩
  · change Q.comap ((algebraMap A S).comp (algebraMap R A)) = q
    rw [← Ideal.comap_comap, hQA, hqA]
  · let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
      IsOpenImmersion.of_isLocalization (D z.val)
    let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A S))) :=
      IsOpenImmersion.of_isLocalization (1 - r)
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R A) ≫
      CommRingCat.ofHom (algebraMap A S)))
    rw [Spec.map_comp]
    infer_instance
  · change I.map ((algebraMap A S).comp (algebraMap R A)) = _
    rw [← Ideal.map_map]
    exact hgen

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CenterPointedFrame.Construction
