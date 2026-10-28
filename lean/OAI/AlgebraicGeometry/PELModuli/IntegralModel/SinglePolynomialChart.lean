import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.ChartCoordinates

/-! # Single Polynomial Chart -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SinglePolynomialChart

noncomputable section

/-! The single projective Laurent chart map is ordinary polynomial
dehomogenization, with the affine base coefficient transport explicit. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

namespace PolarizationEmbedding

universe u v
variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] {n : ℕ}

theorem singlePolynomialChartExponent_self (i : Fin (n + 1)) :
    SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartExponent (fun _ : Fin 1 => i) (Finsupp.single i 1) = 0 := by
  apply Subtype.ext
  ext j
  simp [SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartExponent, Finsupp.single_eq_of_ne j.property]

theorem singlePolynomialChartExponent_ne (i j : Fin (n + 1)) (hj : j ≠ i) :
    SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartExponent (fun _ : Fin 1 => i) (Finsupp.single j 1) =
      SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun _ : Fin 1 => i))
        (Finsupp.single (⟨j, hj⟩ : {k : Fin (n + 1) // k ≠ i}) 1) := by
  classical
  apply Subtype.ext
  ext k
  rw [SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap_apply]
  change ((Finsupp.single j 1 : Fin (n + 1) →₀ ℕ) k.val : ℤ) = _
  by_cases hk : k = ⟨j, hj⟩
  · subst k
    simp
  · have hval : k.val ≠ j := fun h => hk (Subtype.ext h)
    simp [Finsupp.single_eq_of_ne hval, Finsupp.single_eq_of_ne hk]

theorem singlePolynomialChart_dehomogenize (i : Fin (n + 1))
    (p : MvPolynomial (Fin (n + 1)) R) :
    AddMonoidAlgebra.mapDomain
        (SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun _ : Fin 1 => i))).toAddMonoidHom
        (SheafCohomology.Projective.SpaceChart.MvPolynomial.dehomogenizeAux R i p) =
      SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartRingHom R (fun _ : Fin 1 => i) p := by
  classical
  let φ := (AddMonoidAlgebra.mapDomainRingHom R
    (SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun _ : Fin 1 => i))).toAddMonoidHom).comp
      (SheafCohomology.Projective.SpaceChart.MvPolynomial.dehomogenizeAux R i)
  have h : φ = SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartRingHom R (fun _ : Fin 1 => i) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change AddMonoidAlgebra.mapDomain _ (SheafCohomology.Projective.SpaceChart.MvPolynomial.dehomogenizeAux R i (C r)) = _
      rw [SheafCohomology.Projective.SpaceChart.MvPolynomial.dehomogenizeAux_C]
      change AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single 0 r) =
        SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartRingHom R (fun _ : Fin 1 => i) (monomial 0 r)
      rw [AddMonoidAlgebra.mapDomain_single, SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartRingHom_monomial, map_zero, map_zero]
    · intro j
      by_cases hj : j = i
      · subst j
        change (AddMonoidAlgebra.mapDomainRingHom R _)
          (SheafCohomology.Projective.SpaceChart.MvPolynomial.dehomogenizeAux R i (X i)) = _
        rw [SheafCohomology.Projective.SpaceChart.MvPolynomial.dehomogenizeAux_X_self, map_one]
        change 1 = SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartRingHom R (fun _ : Fin 1 => i) (monomial (Finsupp.single i 1) 1)
        rw [SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartRingHom_monomial, singlePolynomialChartExponent_self]
        rfl
      · change AddMonoidAlgebra.mapDomain _ (SheafCohomology.Projective.SpaceChart.MvPolynomial.dehomogenizeAux R i (X j)) = _
        rw [SheafCohomology.Projective.SpaceChart.MvPolynomial.dehomogenizeAux_X_ne R i hj]
        change AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single
          (Finsupp.single (⟨j, hj⟩ : {k : Fin (n + 1) // k ≠ i}) 1) 1) =
          SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartRingHom R (fun _ : Fin 1 => i) (monomial (Finsupp.single j 1) 1)
        rw [AddMonoidAlgebra.mapDomain_single, SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartRingHom_monomial,
          singlePolynomialChartExponent_ne i j hj]
        rfl
  exact RingHom.congr_fun h p

theorem polynomialChartRingHom_mapRingEquiv (e : R ≃+* S) (i : Fin (n + 1))
    (p : MvPolynomial (Fin (n + 1)) R) :
    AddMonoidAlgebra.mapRingEquiv _ e (SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartRingHom R (fun _ : Fin 1 => i) p) =
      SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartRingHom S (fun _ : Fin 1 => i) (MvPolynomial.map e.toRingHom p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d r =>
    rw [MvPolynomial.map_monomial, SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartRingHom_monomial,
      SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartRingHom_monomial, AddMonoidAlgebra.mapRingEquiv_single]
    rfl
  | add p q hp hq => simp only [map_add, hp, hq]

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SinglePolynomialChart
