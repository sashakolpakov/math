import OAI.AlgebraicGeometry.GroupSchemes.CoordinatePoints
import OAI.AlgebraicGeometry.GroupSchemes.LocalObstruction

/-! # Finite Algebra -/

namespace OAI.AlgebraicGeometry.GroupSchemes.FiniteAlgebra.EtaleFinite

noncomputable section

/-! Finite algebras over an algebraically closed field and their rational points. -/

universe u

variable (k A : Type u) [Field k] [IsAlgClosed k] [CommRing A]
  [Algebra k A] [Module.Finite k A]

/-- Every maximal ideal of a finite algebra over an algebraically closed field gives a k-point. -/
def pointOfMaximal (I : MaximalSpectrum A) : A →ₐ[k] k :=
  (AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ I.asIdeal))
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k))).symm.toAlgHom.comp
      (Ideal.Quotient.mkₐ k I.asIdeal)

/-- The point just constructed has the specified maximal ideal as kernel. -/
theorem pointOfMaximal_ker (I : MaximalSpectrum A) :
    RingHom.ker (pointOfMaximal k A I).toRingHom = I.asIdeal := by
  let e := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ I.asIdeal))
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k))
  change RingHom.ker (e.symm.toRingEquiv.toRingHom.comp (Ideal.Quotient.mk I.asIdeal)) = _
  rw [RingHom.ker_comp_of_injective _ e.symm.injective, Ideal.mk_ker]

/-- A finite algebra with an augmentation and a unique k-point is local. -/
theorem isLocalRing_of_unique_point (ε : A →ₐ[k] k)
    (hpoint : ∀ f : A →ₐ[k] k, f = ε) : IsLocalRing A := by
  have : Nontrivial A := ε.toRingHom.domain_nontrivial
  have : Subsingleton (MaximalSpectrum A) := ⟨by
    intro I J
    apply MaximalSpectrum.ext
    rw [← pointOfMaximal_ker k A I, ← pointOfMaximal_ker k A J,
      hpoint (pointOfMaximal k A I), hpoint (pointOfMaximal k A J)]⟩
  exact IsLocalRing.of_singleton_maximalSpectrum

omit [IsAlgClosed k] in
/-- An augmentation is the only point of a local finite algebra. -/
theorem point_eq_of_local [IsLocalRing A] (ε f : A →ₐ[k] k) : f = ε := by
  ext x
  have hn := LocalObstruction.FiniteEtale.nilpotent_of_augmentation_zero k A ε
    (x - algebraMap k A (ε x)) (by simp)
  have hz := (hn.map f).eq_zero
  simpa [sub_eq_zero] using hz

/-- A finite reduced algebra over an algebraically closed field is split étale. -/
theorem split_of_reduced [IsReduced A] : Algebra.IsFiniteSplit k A := by
  have : IsArtinianRing A := isArtinian_of_tower k inferInstance
  let e : A ≃ₐ[k] (MaximalSpectrum A → k) :=
    ((IsArtinianRing.equivPi A).restrictScalars k).trans
      (AlgEquiv.piCongrRight fun I =>
        (AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ I.asIdeal))
          (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k))).symm)
  exact Algebra.IsFiniteSplit.of_algEquiv e.symm

omit [IsAlgClosed k] in
/-- A one-dimensional algebra is the base field and hence split. -/
theorem split_of_rank_one (hdim : Module.finrank k A = 1) : Algebra.IsFiniteSplit k A :=
  Algebra.IsFiniteSplit.of_algEquiv (AlgEquiv.ofBijective (Algebra.ofId k A)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdim))

/-- A point of a finite algebra in any domain factors uniquely through the algebraically closed base. -/
theorem scalar_comp_bijective {S : Type*} [CommRing S] [IsDomain S] [Algebra k S] :
    Function.Bijective ((Algebra.ofId k S).comp : (A →ₐ[k] k) → A →ₐ[k] S) := by
  constructor
  · intro f g h
    ext x
    apply (algebraMap k S).injective
    exact AlgHom.congr_fun h x
  · intro f
    have : Module.Finite k f.range := Module.Finite.of_surjective f.rangeRestrict.toLinearMap
      f.rangeRestrict_surjective
    let e : k ≃ₐ[k] f.range := AlgEquiv.ofBijective (Algebra.ofId k f.range)
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k))
    refine ⟨e.symm.toAlgHom.comp f.rangeRestrict, ?_⟩
    ext x
    exact congrArg Subtype.val (e.apply_symm_apply (f.rangeRestrict x))

end

end OAI.AlgebraicGeometry.GroupSchemes.FiniteAlgebra.EtaleFinite
