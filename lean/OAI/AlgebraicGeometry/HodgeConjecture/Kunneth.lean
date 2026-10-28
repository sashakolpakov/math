import OAI.AlgebraicTopology.Kunneth.Add
import OAI.AlgebraicGeometry.HodgeConjecture.TensorContraction
import OAI.AlgebraicGeometry.HodgeConjecture.SurfaceConstructionQ
import OAI.AlgebraicTopology.Kunneth.ProjectiveFinitenessLe

/-! # Kunneth -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.Kunneth.CM.SurfaceConstruction

noncomputable section

/-! Nonvanishing of the actual complex exterior cup, derived from the
checked canonical Kunneth equivalence and coefficient finiteness. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct DirectSum

theorem complex_cohomology_finite (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) :
    FiniteDimensional ℂ (X.complexCohomology n) := by
  let : FiniteDimensional ℚ (X.rationalCohomology n) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.projective_cohomology_finite X n
  exact Module.Finite.of_surjective
    (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) n)
    (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_surjective (Betti.Scheme.schemePointSpace X.toOver) n)

theorem complex_homology_finite (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) :
    FiniteDimensional ℂ
      ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver)).homology n) := by
  let : FiniteDimensional ℂ (X.complexCohomology n) := complex_cohomology_finite X n
  exact AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.finite_homology_of_finite_cohomology
    (Betti.Scheme.schemePointSpace X.toOver) n

theorem complex_degree_le (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (a : X.complexCohomology n) (ha : a ≠ 0) : n ≤ 2 * X.complexDimension := by
  by_contra hn
  have hn' : 2 * X.complexDimension < n := by omega
  let : FiniteDimensional ℚ (X.rationalCohomology n) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite X n
  let : Subsingleton (X.rationalCohomology n) := ModuleCat.subsingleton_of_isZero
    (X.singularCohomology_isZero_above_dimension n hn')
  let : Subsingleton (ComplexMultiplication.WeightOne.CM.Complexification (X.rationalCohomology n)) := inferInstance
  obtain ⟨t, ht⟩ := ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_surjective (Betti.Scheme.schemePointSpace X.toOver) n a
  have ht0 : t = 0 := Subsingleton.elim _ _
  rw [ht0, map_zero] at ht
  exact ha ht.symm

theorem topological_exteriorCup_ne_zero {k : Type} [Field k]
    (X Y : TopCat.{0})
    [∀ n, FiniteDimensional k ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) X).homology n)]
    [∀ n, FiniteDimensional k ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y).homology n)]
    (p q : ℕ) (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of k k) X p)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of k k) Y q) (ha : a ≠ 0) (hb : b ≠ 0) :
    AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := k) (TopCat.of (X × Y)) p q
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of k k) TopCat.prodFst p a)
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of k k) TopCat.prodSnd q b) ≠ 0 := by
  classical
  intro hz
  have h := AlgebraicTopology.Kunneth.CanonicalCohomology.Construction.CanonicalCohomologyKunneth.canonicalCohomologyEquiv_lof_add X Y p q a b
  rw [hz] at h
  have hz' :=
    (AlgebraicTopology.Kunneth.CanonicalCohomology.Construction.CanonicalCohomologyKunneth.canonicalCohomologyEquiv X Y (p + q)).injective
      (h.trans (map_zero _).symm)
  have ht := congrArg
    (DirectSum.component k (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.DegreePairs (p + q))
      (fun ij => AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of k k) X ij.val.1 ⊗[k]
        AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of k k) Y ij.val.2) ⟨(p, q), rfl⟩) hz'
  simp only [DirectSum.component.lof_self, map_zero] at ht
  exact TensorContraction.CM.SurfaceConstruction.simpleTensor_ne_zero k ha hb ht

theorem complex_exteriorCup_ne_zero
    {X Y Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
    (hprod : IsLimit (BinaryFan.mk πX πY))
    (p q : ℕ) (a : X.complexCohomology p) (b : Y.complexCohomology q)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace Z.toOver) p q
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) p πX a)
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) q πY b) ≠ 0 := by
  let : ∀ n, FiniteDimensional ℂ
      ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver)).homology n) :=
    complex_homology_finite X
  let : ∀ n, FiniteDimensional ℂ
      ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℂ) (Betti.Scheme.schemePointSpace Y.toOver)).homology n) :=
    complex_homology_finite Y
  let e := AlgebraicTopology.Kunneth.Add.Construction.productPointIso πX πY hprod
  let ec := (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyFunctor (ModuleCat.of ℂ ℂ) (p + q)).mapIso e.op
  have hnonzero := topological_exteriorCup_ne_zero
    (Betti.Scheme.schemePointSpace X.toOver) (Betti.Scheme.schemePointSpace Y.toOver) p q a b ha hb
  intro hz
  apply hnonzero
  apply ec.toLinearEquiv.injective
  erw [map_zero]
  change AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) e.hom (p + q) _ = 0
  rw [AlgebraicTopology.Kunneth.CupPullbackSingular.Construction.CupPullback.singularCohomologyCup_pullback]
  change AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace Z.toOver) p q
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) e.hom p
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) TopCat.prodFst p a))
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) e.hom q
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) TopCat.prodSnd q b)) = 0
  have hf := AlgebraicTopology.Kunneth.Add.Construction.productPointIso_fst πX πY hprod
  have hg := AlgebraicTopology.Kunneth.Add.Construction.productPointIso_snd πX πY hprod
  have hpull : ∀ {U V W : TopCat.{0}} (f : U ⟶ V) (g : V ⟶ W) n
      (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) W n),
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) f n
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) g n c) =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) (f ≫ g) n c := by
    intro U V W f g n c
    rw [AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp]
    rfl
  rw [hpull, hpull]
  change AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace Z.toOver) p q
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ)
      ((AlgebraicTopology.Kunneth.Add.Construction.productPointIso πX πY hprod).hom ≫ TopCat.prodFst) p a)
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ)
      ((AlgebraicTopology.Kunneth.Add.Construction.productPointIso πX πY hprod).hom ≫ TopCat.prodSnd) q b) = 0
  rw [hf, hg]
  exact hz

theorem rational_exteriorCup_ne_zero
    {X Y Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
    (hprod : IsLimit (BinaryFan.mk πX πY))
    (p q : ℕ) (a : X.rationalCohomology p) (b : Y.rationalCohomology q)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace Z.toOver) p q
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) p πX a)
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) q πY b) ≠ 0 := by
  classical
  intro hz
  have h := AlgebraicTopology.Kunneth.Add.Construction.kunnethMap_lof_tmul πX πY (p + q) ⟨(p, q), rfl⟩ a b
  change AlgebraicTopology.Kunneth.Add.Construction.kunnethMap πX πY (p + q) _ = _ at h
  have hz' : AlgebraicTopology.Kunneth.Add.Construction.exteriorProduct πX πY p q a b = 0 := hz
  simp only [hz', cast_eq] at h
  have hinj := (AlgebraicTopology.Kunneth.Add.Construction.kunnethMap_bijective πX πY hprod (p + q)).injective
  have hs := hinj (h.trans (map_zero _).symm)
  have ht := congrArg
    (DirectSum.component ℚ (AlgebraicTopology.Kunneth.Add.Construction.DegreePairs (p + q))
      (fun ij => AlgebraicTopology.Kunneth.Add.Construction.KunnethSummand X Y ij.val) ⟨(p, q), rfl⟩) hs
  simp only [DirectSum.component.lof_self, map_zero] at ht
  exact TensorContraction.CM.SurfaceConstruction.simpleTensor_ne_zero ℚ ha hb ht

end

end OAI.AlgebraicGeometry.HodgeConjecture.Kunneth.CM.SurfaceConstruction
