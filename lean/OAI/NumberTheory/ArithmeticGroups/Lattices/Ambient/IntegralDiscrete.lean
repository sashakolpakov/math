import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.OperatorBracketStability

/-! # Integral Discrete -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.IntegralDiscrete.Construction

noncomputable section

/-! The ambient integral operator subgroup is discrete, by its
faithful action on the finite integral basis frame. -/

open scoped Classical

theorem ambientIntegralOperatorGroup_discrete
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) : DiscreteTopology (VolumeOperatorSiegelCover.Construction.ambientIntegralOperatorGroup b) := by
  let Λ := Submodule.span ℤ (Set.range b)
  let : DiscreteTopology Λ := inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range b.toBasis)))
  let f : VolumeOperatorSiegelCover.Construction.ambientIntegralOperatorGroup b → Fin m → Λ := fun g i =>
    ⟨g.val.val.val (b i), Integral.OperatorBracketStability.Construction.ambientIntegralOperatorGroup_maps_lattice b g.val g.property (b i)
      (Submodule.subset_span (Set.mem_range_self i))⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · apply continuous_pi
    intro i
    exact ((Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).clm_apply
      continuous_const).subtype_mk _
  · intro g h he
    have hlin : g.val.val.val.toLinearMap = h.val.val.val.toLinearMap := by
      apply b.toBasis.ext
      intro i
      exact congrArg (fun u : Fin m → Λ => (u i).val) he
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    ext x
    exact LinearMap.congr_fun hlin x

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.IntegralDiscrete.Construction
