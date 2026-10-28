import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.RegularPowerSection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.TwistEulerPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyFiniteDescent

/-! # Twist Cohomology Bound -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.TwistCohomologyBound

noncomputable section

/-! For a coherent sheaf on a proper scheme over an infinite field, a known ample-twist Euler polynomial bounds its cohomological degree. The proof constructs regular sections, uses their actual cokernels to lower polynomial degree, and descends from a sufficiently late Serre-vanishing twist. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}

theorem ample_exists_acyclic_tensor_iterate
    (p : X ⟶ Spec (.of K)) [IsProper p] (L : Line.Bundles.LineBundle X) (hL : L.IsAmple)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ B : ℕ, ∀ q : ℕ, IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap p) (q + 1)).obj
        ((Iterated.EquivalenceCohomology.iterateAutoEquivalence (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence L) B).functor.obj M)) := by
  obtain ⟨E⟩ := hL.exists_powerProjectiveEmbedding p
  obtain ⟨B, hB⟩ := E.tensorPowers_eventually_vanish M
  refine ⟨B * E.degree, fun q => ?_⟩
  exact ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) (q + 1)).mapIso
    (LineBundle.TwistIteration.lineBundleTwistIterationIso L (B * E.degree) M)).isZero_iff.mpr (hB B le_rfl q)

theorem coherentCohomology_vanish_above_eulerPolynomial_degree [Infinite K]
    (p : X ⟶ Spec (.of K)) [IsProper p]
    (L : Line.Bundles.LineBundle X) (hL : L.IsAmple)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (P : Polynomial ℚ) (hP : Coherent.TwistEulerPolynomial.HasCoherentTwistEulerPolynomial p M L P)
    (q : ℕ) (hq : P.natDegree < q) :
    IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj M) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian X := ⟨⟩
  have bound (n : ℕ) :
      ∀ (T : Line.Bundles.LineBundle X), T.IsAmple →
      ∀ (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
        (Q : Polynomial ℚ), Coherent.TwistEulerPolynomial.HasCoherentTwistEulerPolynomial p F T Q → Q.natDegree = n →
      ∀ j : ℕ, n < j → IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
        (Coefficient.ModulePresheaf.schemeCoefficientMap p) j).obj F) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T hT F hFq hFt Q hQ hdeg j hj
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
      obtain ⟨d, hd, s, hs⟩ := hT.exists_power_section_injective_on_coherent p F
      let U := T.tensorPower d
      have hU : U.IsAmple := hT.tensorPower d hd
      let E := LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence U
      have : Mono (Module.SectionMultiplication.moduleSectionMultiply U F s) := hs
      let a : F ⟶ E.functor.obj F := LineBundle.TwistIteration.regularSectionToRightTensor U F s
      have : Mono a := LineBundle.TwistIteration.regularSectionToRightTensor_mono U F s
      have : (E.functor.obj F).IsQuasicoherent := LineBundle.TensorEquivalenceCoherence.lineBundleRightTensor_quasicoherent U F
      have : (E.functor.obj F).IsFiniteType := LineBundle.TensorEquivalenceCoherence.lineBundleRightTensor_finiteType U F
      have : (cokernel a).IsQuasicoherent := Quasicoherent.Cokernels.module_quasicoherent_cokernel a
      have : (cokernel a).IsFiniteType := Quasicoherent.QuotientFiniteType.quasicoherent_cokernel_finiteType a
      let D := HilbertConstruction.Polynomial.FirstDifference.polynomialFirstDifference (Q.comp (Polynomial.C (d : ℚ) * Polynomial.X))
      have hD : Coherent.TwistEulerPolynomial.HasCoherentTwistEulerPolynomial p (cokernel a) U D := (hQ.power d).cokernel a
      have hdQ : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
      have hvan : ∀ m, IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
          (Coefficient.ModulePresheaf.schemeCoefficientMap p) r).obj ((Iterated.EquivalenceCohomology.iterateAutoEquivalence E m).functor.obj (cokernel a))) := by
        by_cases hn : n = 0
        · have hDzero : D = 0 := by
            apply HilbertConstruction.Polynomial.FirstDifference.polynomialFirstDifference_eq_zero_of_natDegree_zero
            rw [HilbertConstruction.Polynomial.FirstDifference.polynomial_nonzero_dilation_natDegree Q (d : ℚ) hdQ, hdeg, hn]
          obtain ⟨EU⟩ := hU.exists_powerProjectiveEmbedding p
          have hzero : IsZero (cokernel a) :=
            Coherent.TwistEulerPolynomial.HasCoherentTwistEulerPolynomial.isZero_of_polynomial_zero EU (hDzero ▸ hD)
          intro m
          exact (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) r).map_isZero
            ((Iterated.EquivalenceCohomology.iterateAutoEquivalence E m).functor.map_isZero hzero)
        · have hDlt : D.natDegree < n :=
            (HilbertConstruction.Polynomial.FirstDifference.polynomialFirstDifference_dilation_natDegree_lt Q (by omega) (d : ℚ) hdQ).trans_eq hdeg
          intro m
          let G := Tensor.ProductSheaf.tensorModule (cokernel a) (U.tensorPower m).sheaf
          have : G.IsQuasicoherent := LineBundle.TensorCoherence.tensorModuleRight_lineBundle_quasicoherent _ _
          have : G.IsFiniteType := LineBundle.TensorCoherence.tensorModuleRight_lineBundle_finiteType _ _
          let R := D.comp (Polynomial.X + Polynomial.C (m : ℚ))
          have hR : R.natDegree = D.natDegree := by
            rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
          have hRlt : R.natDegree < n := hR.trans_lt hDlt
          have hRG : Coherent.TwistEulerPolynomial.HasCoherentTwistEulerPolynomial p G U R := hD.shift m
          have hG := ih R.natDegree hRlt U hU G R hRG rfl r (by omega)
          exact ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) r).mapIso
            (LineBundle.TwistIteration.lineBundleTwistIterationIso U m (cokernel a))).isZero_iff.mpr hG
      obtain ⟨B, hB⟩ := ample_exists_acyclic_tensor_iterate p U hU F
      exact CohomologyFiniteDescent.ZariskiCohomology.coefficientCohomology_vanish_of_iterated_cokernel_at
        (Coefficient.ModulePresheaf.schemeCoefficientMap p) E a r B hvan (hB r)
  exact bound P.natDegree L hL M P hP rfl q hq

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.TwistCohomologyBound
