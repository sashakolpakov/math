import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TwoFormEnergy
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HarmonicOneForms
import OAI.AlgebraicTopology.DeRham.Comparison.Projective

/-! # One Spanning -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneSpanning.CM.Construction

noncomputable section

/-! Every projective degree-one de Rham class is a sum of classes of
closed forms of types (1,0) and (0,1). -/

theorem projective_hodge_split_one (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1) :
    ∃ (α β : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1),
      Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0 α.val.val ∧
      Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 0 1 β.val.val ∧
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass V.analyticModel V.analyticSpace 1 form =
        Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass V.analyticModel V.analyticSpace 1 α +
          Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass V.analyticModel V.analyticSpace 1 β := by
  obtain ⟨f, hf, hc⟩ := HarmonicOneForms.CM.Construction.exists_closed_coclosed_representative V (CompactMetricCover.CM.Construction.projectiveCompactMetricCover V)
    (stdOrthonormalBasis ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) form.val form.property
  have hh := (TwoFormEnergy.CM.Construction.closed_coclosed_oneForm_parts_closed V _ hf hc).1
  rw [map_sub, map_sub] at hh
  exact OneFormProjection.CM.Construction.hodge_split_of_scalar_correction form f (sub_eq_zero.mp hh).symm

theorem pureDeRham_one_sup_top (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    V.pureDeRhamSubspace 1 0 ⊔ V.pureDeRhamSubspace 0 1 = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨form, rfl⟩ := Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamFormClass_surjective V.analyticModel V.analyticSpace 1 x
  obtain ⟨α, β, hα, hβ, hclass⟩ := projective_hodge_split_one V form
  apply Submodule.mem_sup.mpr
  refine ⟨_, (AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.mem_manifoldPureDeRhamImage_iff V.analyticModel V.analyticSpace 1 0 _).mpr ⟨α, hα, rfl⟩,
    _, (AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.mem_manifoldPureDeRhamImage_iff V.analyticModel V.analyticSpace 0 1 _).mpr ⟨β, hβ, rfl⟩,
    hclass.symm⟩

theorem pureBetti_one_sup_top (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    V.pureBettiSubspace 1 0 ⊔ V.pureBettiSubspace 0 1 = ⊤ := by
  change (V.pureDeRhamSubspace 1 0).map (V.deRhamBettiIso 1).hom.hom ⊔
    (V.pureDeRhamSubspace 0 1).map (V.deRhamBettiIso 1).hom.hom = ⊤
  rw [← Submodule.map_sup, pureDeRham_one_sup_top, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (V.deRhamBettiIso 1).toLinearEquiv.surjective

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneSpanning.CM.Construction
