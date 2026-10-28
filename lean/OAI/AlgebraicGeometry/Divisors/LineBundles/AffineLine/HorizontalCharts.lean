import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.GenericPoint
import OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.GenericFiber

/-! # Horizontal Charts -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.HorizontalCharts.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: actual polynomial charts for points over the generic point of an integral base -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme.{0}) [IsIntegral X]

theorem affineLinePolynomialChart_base_generic_iff (U : X.affineOpens) [Nonempty U.1]
    (P : Spec (.of (Polynomial Γ(X, U.1)))) :
    Charts.BundleCycles.affineLineProjection X (Charts.BundleCycles.affineLinePolynomialChart X U P) = genericPoint X ↔
      LineBundles.Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1) P = genericPoint (Spec Γ(X, U.1)) := by
  have hbase := congrArg (fun k => k P) (Charts.BundleCycles.affineLinePolynomialChart_toBase X U)
  have hg := genericPoint_eq_of_isOpenImmersion U.2.fromSpec
  constructor
  · intro h
    apply U.2.fromSpec.isOpenEmbedding.injective
    exact hbase.symm.trans (h.trans hg.symm)
  · intro h
    exact hbase.trans ((congrArg U.2.fromSpec h).trans hg)

theorem affineLineHorizontalPoint_exists_chart (y : Charts.BundleCycles.affineLine X)
    (hy : Charts.BundleCycles.affineLineProjection X y = genericPoint X) (hne : y ≠ genericPoint (Charts.BundleCycles.affineLine X)) :
    ∃ (U : X.affineOpens) (_ : Nonempty U.1) (P : Spec (.of (Polynomial Γ(X, U.1)))),
      Charts.BundleCycles.affineLinePolynomialChart X U P = y ∧ P.asIdeal ≠ ⊥ ∧ P.asIdeal.comap Polynomial.C = ⊥ := by
  obtain ⟨U, P, rfl⟩ := Charts.BundleCycles.affineLinePolynomialChart_covers X y
  have hu : U.2.fromSpec (LineBundles.Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1) P) ∈ (U.1 : Set X) :=
    U.2.range_fromSpec ▸ Set.mem_range_self (LineBundles.Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1) P)
  have : Nonempty U.1 := ⟨⟨_, hu⟩⟩
  refine ⟨U, inferInstance, P, rfl, ?_, ?_⟩
  · intro hp
    apply hne
    have hP : P = genericPoint (Spec (.of (Polynomial Γ(X, U.1)))) := by
      rw [genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext hp
    exact (congrArg (Charts.BundleCycles.affineLinePolynomialChart X U) hP).trans (genericPoint_eq_of_isOpenImmersion _)
  · have hp := (affineLinePolynomialChart_base_generic_iff X U P).mp hy
    rw [genericPoint_eq_bot_of_affine] at hp
    exact congrArg (fun p : Spec Γ(X, U.1) => p.asIdeal) hp

end

/-! # LineBundleCycles: actual horizontal point-divisor relations on the relative affine line over an integral scheme -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]

theorem affineLineHorizontalPoint_relation (y : Charts.BundleCycles.affineLine X)
    (hy : Charts.BundleCycles.affineLineProjection X y = genericPoint X) (hne : y ≠ genericPoint (Charts.BundleCycles.affineLine X)) :
    ∃ g : (Charts.BundleCycles.affineLine X).functionField, g ≠ 0 ∧
      ∀ q ∈ (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Charts.BundleCycles.affineLine X) g - Finsupp.single y 1).support,
        Charts.BundleCycles.affineLineProjection X q ≠ genericPoint X := by
  obtain ⟨U, hU, P, rfl, hP, hbase⟩ := affineLineHorizontalPoint_exists_chart X y hy hne
  let := hU
  obtain ⟨a, ha, _, hvertical⟩ := LineBundles.Polynomial.GenericFiber.BundleCycles.polynomialHorizontalPoint_relation Γ(X, U.1) P hP hbase
  let j := Charts.BundleCycles.affineLinePolynomialChart X U
  let e := RationalDivisorRestriction.BundleCycles.openFunctionFieldIso j
  let g := e.inv a
  have hg : g ≠ 0 := (map_ne_zero_iff _ e.symm.commRingCatIsoToRingEquiv.injective).mpr ha
  have hfield : RationalDivisorRestriction.BundleCycles.openFunctionFieldMap j g = a := Iso.inv_hom_id_apply e a
  refine ⟨g, hg, ?_⟩
  intro q hq hgen
  have hmem : q ∈ Set.range j := by
    rw [Charts.BundleCycles.affineLinePolynomialChart_range]
    change Charts.BundleCycles.affineLineProjection X q ∈ (U.1 : Set X)
    rw [hgen]
    exact ((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr (by simpa using hU)
  obtain ⟨Q, rfl⟩ := hmem
  have hbQ := (affineLinePolynomialChart_base_generic_iff X U Q).mp hgen
  rw [genericPoint_eq_bot_of_affine] at hbQ
  have hbaseQ : Q.asIdeal.comap Polynomial.C = ⊥ := congrArg (fun p : Spec Γ(X, U.1) => p.asIdeal) hbQ
  apply hvertical Q _ hbaseQ
  apply Finsupp.mem_support_iff.mpr
  intro hz
  apply Finsupp.mem_support_iff.mp hq
  have hord := RationalDivisorRestriction.BundleCycles.ord_openImmersion j g Q
  rw [hfield] at hord
  have hs : Finsupp.single (j P) (1 : ℚ) (j Q) = Finsupp.single P 1 Q :=
    Finsupp.single_apply_left j.isOpenEmbedding.injective P Q 1
  change (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Charts.BundleCycles.affineLine X) g - Finsupp.single (j P) 1 : Charts.BundleCycles.affineLine X →₀ ℚ) (j Q) = 0
  rw [Finsupp.sub_apply, RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, ← hord, hs]
  exact hz

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.HorizontalCharts.BundleCycles
