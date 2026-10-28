import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneSpanning
import Mathlib.LinearAlgebra.Prod

/-! # Canonical One Forms -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CanonicalOneForms.CM.Construction

noncomputable section

/-! The Hodge decomposition gives canonical actual closed one-form
representatives, as sums of their unique holomorphic and antiholomorphic forms. -/

abbrev HodgeOneFormPairs (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :=
  AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms V.analyticModel V.analyticSpace 1 0 ×
    AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms V.analyticModel V.analyticSpace 0 1

def hodgeOnePairClass (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    HodgeOneFormPairs V →ₗ[ℂ] V.deRhamCohomology 1 :=
  (AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.manifoldPureFormClass V.analyticModel V.analyticSpace 1 0).coprod
    (AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.manifoldPureFormClass V.analyticModel V.analyticSpace 0 1)

theorem hodgeOnePairClass_bijective (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Function.Bijective (hodgeOnePairClass V) := by
  have hh := LinearMap.ker_eq_bot.mpr
    (HolomorphicPrimitive.CM.Construction.holomorphic_formClass_injective (E := V.analyticModel) (M := V.analyticSpace))
  have ha := LinearMap.ker_eq_bot.mpr
    (HolomorphicPrimitive.CM.Construction.antiholomorphic_formClass_injective (E := V.analyticModel) (M := V.analyticSpace))
  constructor
  · rw [← LinearMap.ker_eq_bot, hodgeOnePairClass,
      LinearMap.ker_coprod_of_disjoint_range, hh, ha, Submodule.prod_bot]
    rw [AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.range_manifoldPureFormClass, AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.range_manifoldPureFormClass]
    exact Intersection.CM.Construction.pureDeRham_one_disjoint
  · rw [← LinearMap.range_eq_top, hodgeOnePairClass, LinearMap.range_coprod,
      AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.range_manifoldPureFormClass, AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.range_manifoldPureFormClass]
    exact OneSpanning.CM.Construction.pureDeRham_one_sup_top V

def hodgeOnePairEquiv (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    HodgeOneFormPairs V ≃ₗ[ℂ] V.deRhamCohomology 1 :=
  LinearEquiv.ofBijective (hodgeOnePairClass V) (hodgeOnePairClass_bijective V)

def hodgeOnePairSum (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    HodgeOneFormPairs V →ₗ[ℂ] Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1 :=
  (AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms V.analyticModel V.analyticSpace 1 0).subtype.coprod
    (AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms V.analyticModel V.analyticSpace 0 1).subtype

theorem hodgeOnePairSum_class (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : HodgeOneFormPairs V) :
    V.deRhamClass 1 (hodgeOnePairSum V p) = hodgeOnePairClass V p := by
  change Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass V.analyticModel V.analyticSpace 1 (p.1.val + p.2.val) = _
  exact map_add _ _ _

def canonicalDeRhamOneRepresentative (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    V.deRhamCohomology 1 →ₗ[ℂ] Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1 :=
  (hodgeOnePairSum V).comp (hodgeOnePairEquiv V).symm.toLinearMap

theorem canonicalDeRhamOneRepresentative_class (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (c : V.deRhamCohomology 1) :
    V.deRhamClass 1 (canonicalDeRhamOneRepresentative V c) = c :=
  (hodgeOnePairSum_class V ((hodgeOnePairEquiv V).symm c)).trans
    ((hodgeOnePairEquiv V).apply_symm_apply c)

def hodgeClosedOneForms (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Submodule ℂ (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1) :=
  AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms V.analyticModel V.analyticSpace 1 0 ⊔
    AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms V.analyticModel V.analyticSpace 0 1

theorem canonicalDeRhamOneRepresentative_mem (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (c : V.deRhamCohomology 1) : canonicalDeRhamOneRepresentative V c ∈ hodgeClosedOneForms V := by
  let p := (hodgeOnePairEquiv V).symm c
  exact Submodule.mem_sup.mpr ⟨p.1.val, p.1.property, p.2.val, p.2.property, rfl⟩

theorem hodgeClosedOne_class_injective (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1)
    (ha : a ∈ hodgeClosedOneForms V) (hb : b ∈ hodgeClosedOneForms V)
    (hab : V.deRhamClass 1 a = V.deRhamClass 1 b) : a = b := by
  obtain ⟨ah, hah, aa, haa, rfl⟩ := Submodule.mem_sup.mp ha
  obtain ⟨bh, hbh, ba, hba, rfl⟩ := Submodule.mem_sup.mp hb
  have hpair : ((⟨ah, hah⟩, ⟨aa, haa⟩) : HodgeOneFormPairs V) = (⟨bh, hbh⟩, ⟨ba, hba⟩) :=
    (hodgeOnePairClass_bijective V).1
      ((hodgeOnePairSum_class V (⟨ah, hah⟩, ⟨aa, haa⟩)).symm.trans
        (hab.trans (hodgeOnePairSum_class V (⟨bh, hbh⟩, ⟨ba, hba⟩))))
  exact congrArg (hodgeOnePairSum V) hpair

theorem canonicalDeRhamOneRepresentative_of_hodge (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1)
    (ha : a ∈ hodgeClosedOneForms V) :
    canonicalDeRhamOneRepresentative V (V.deRhamClass 1 a) = a :=
  hodgeClosedOne_class_injective V _ a (canonicalDeRhamOneRepresentative_mem V _) ha
    (canonicalDeRhamOneRepresentative_class V _)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CanonicalOneForms.CM.Construction
