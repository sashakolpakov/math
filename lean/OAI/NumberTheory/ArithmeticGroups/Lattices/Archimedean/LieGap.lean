import OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.LieMem

/-! # Lie Gap -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.LieGap.Construction

noncomputable section

/-! The characteristic-invariant lower bound applies to the actual
Minkowski Lie-lattice representation of an anisotropic group. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding

theorem lieMixedLattice_eq_integralLieMixedSet
    {k : Type} [Field k] [NumberField k] (G : Algebraic.ConnectedSemisimpleKGroup k) :
    (Lie.MixedLattice.Construction.lieMixedLattice G.matrixGroup : Set (Matrix (Fin G.dimension) (Fin G.dimension) (mixedSpace k))) =
      Lie.CharacteristicGap.Construction.integralLieMixedSet G := by
  ext x
  constructor
  · rintro ⟨A, hA, hAx⟩
    obtain ⟨C, hC⟩ := (Integral.Lie.Construction.mem_integralLieLattice G.matrixGroup A).mp hA
    refine ⟨C, hC.symm ▸ A.property, ?_⟩
    rw [← hAx]
    change A.val.map (mixedEmbedding k) = C.map ((mixedEmbedding k).comp (algebraMap (𝓞 k) k))
    rw [← hC]
    rfl
  · rintro ⟨C, hC, rfl⟩
    let A : Infinitesimal.Action.Construction.infinitesimalStabilizer G.matrixGroup := ⟨C.map (algebraMap (𝓞 k) k), hC⟩
    refine ⟨A, (Integral.Lie.Construction.mem_integralLieLattice G.matrixGroup A).mpr ⟨C, rfl⟩, rfl⟩

theorem anisotropic_archimedeanLie_uniform_gap
    {k : Type} [Field k] [NumberField k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (haniso : Algebraic.IsAnisotropic G) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : ExteriorAction.Construction.fullArchimedeanMatrixGroup G.matrixGroup,
      ∀ x ∈ Lie.MixedLattice.Construction.lieMixedLatticeInSpan G.matrixGroup, x ≠ 0 →
        ε ≤ ‖LieMem.Construction.archimedeanLieRepresentation G.matrixGroup G.connected g x‖ := by
  obtain ⟨ε, hε, hgap⟩ := Lie.CharacteristicGap.Construction.anisotropic_integralLie_uniform_gap G haniso
  refine ⟨ε, hε, fun g x hx hx0 => ?_⟩
  have hxmem : x.val ∈ Lie.CharacteristicGap.Construction.integralLieMixedSet G := by
    rw [← lieMixedLattice_eq_integralLieMixedSet]
    exact hx
  have hxne : x.val ≠ 0 := fun h => hx0 (Subtype.ext h)
  have h := hgap (LieMem.Construction.archimedeanLieUnit G.matrixGroup g) x.val hxmem hxne
  change ε ≤ ‖(LieMem.Construction.archimedeanLieEquiv G.matrixGroup G.connected g x).val‖
  rwa [LieMem.Construction.archimedeanLieEquiv_apply]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.LieGap.Construction
