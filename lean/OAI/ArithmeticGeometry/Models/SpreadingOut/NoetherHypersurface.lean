import OAI.ArithmeticGeometry.Models.SpreadingOut.HypersurfaceChart

/-! # Noether Hypersurface -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.NoetherHypersurface.Construction

noncomputable section

/-! A geometrically integral finite type affine algebra has a dense principal
open isomorphic to a principal open in an absolutely irreducible hypersurface. -/

open scoped TensorProduct

universe u

theorem finiteType_domain_has_hypersurface_open
    (k K A : Type u) [Field k] [CharZero k] [Field K] [Algebra k K]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [IsDomain (K ⊗[k] A)] :
    ∃ (n : ℕ) (p : Polynomial (MvPolynomial (Fin n) k))
      (d : MvPolynomial (Fin n) k) (b : A),
      p.Monic ∧ 0 < p.natDegree ∧ d ≠ 0 ∧ b ≠ 0 ∧
      Irreducible (MvPolynomial.map (algebraMap k K) ((MvPolynomial.finSuccEquiv k n).symm p)) ∧
      Nonempty (Localization.Away (algebraMap (MvPolynomial (Fin n) k) (AdjoinRoot p) d) ≃ₐ[k]
        Localization.Away b) := by
  obtain ⟨n, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin n) k
  let : Algebra P A := g.toRingHom.toAlgebra
  have ht : IsScalarTower k P A := IsScalarTower.of_algebraMap_eq
    (fun x ↦ (g.commutes x).symm)
  have : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hg
  have : Module.Finite P A := (RingHom.finite_algebraMap).mp hfin
  let F := FractionRing P
  have : CharZero F := charZero_of_injective_algebraMap
    (IsFractionRing.injective P F)
  obtain ⟨a, d, hd, ⟨e⟩⟩ := CommonOpenAlgebra.Construction.finite_domain_common_hypersurface_open P A F
  have ha : IsIntegral P a := Algebra.IsIntegral.isIntegral a
  have hb : algebraMap P A d ≠ 0 := by
    change g d ≠ 0
    simpa only [map_zero] using hg.ne hd
  refine ⟨n, minpoly P a, d, algebraMap P A d, minpoly.monic ha,
    minpoly.natDegree_pos ha, hd, hb, ?_, ⟨e.restrictScalars k⟩⟩
  exact HypersurfaceChart.Construction.monogenic_hypersurface_absolute_irreducible k K A n a ha

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.NoetherHypersurface.Construction
