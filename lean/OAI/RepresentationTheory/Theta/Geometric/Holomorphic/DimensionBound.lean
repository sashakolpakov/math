import OAI.AlgebraicGeometry.PELModuli.CMPoints.CountableHolomorphicImage

/-! # Dimension Bound -/

namespace OAI.RepresentationTheory.Theta.Geometric.Holomorphic.DimensionBound

noncomputable section

/-! An injective holomorphic map on a nonempty open set bounds the
dimension of its source by the dimension of its target. -/

open Set _root_.Module

theorem finrank_le_of_holomorphic_injOn
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {f : V → W} {U : Set V} (hU : IsOpen U) (hne : U.Nonempty)
    (hf : DifferentiableOn ℂ f U) (hi : Set.InjOn f U) : finrank ℂ V ≤ finrank ℂ W := by
  obtain ⟨x, _, hx⟩ := AlgebraicGeometry.PELModuli.CMPoints.CountableHolomorphicImage.CountableMaximalRank.exists_injective_point hU hne hf
    (fun y => Set.Subsingleton.countable (show {z : V | z ∈ U ∧ f z = y}.Subsingleton from
      fun z hz w hw => hi hz.1 hw.1 (hz.2.trans hw.2.symm)))
  exact LinearMap.finrank_le_finrank_of_injective (f := (fderiv ℂ f x).toLinearMap) hx

end

end OAI.RepresentationTheory.Theta.Geometric.Holomorphic.DimensionBound
