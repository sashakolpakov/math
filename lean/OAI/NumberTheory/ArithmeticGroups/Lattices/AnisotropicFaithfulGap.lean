import OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointFaithfulGap

/-! # Anisotropic Faithful Gap -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.AnisotropicFaithfulGap.Construction

noncomputable section

/-! Adjoint Mahler representatives and invariant cyclic word minors
give a uniform gap for the faithful arithmetic Minkowski lattice. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding _root_.Module

local instance faithfulGap_normed_discrete
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    @DiscreteTopology (Lie.MixedLattice.Construction.lieMixedLatticeInSpan G)
      (@instTopologicalSpaceSubtype (Lie.MixedLattice.Construction.lieMixedSpan G) _
        (inferInstance : NormedAddCommGroup (Lie.MixedLattice.Construction.lieMixedSpan G)).toUniformSpace.toTopologicalSpace) :=
  Lie.MixedLattice.Construction.lieMixedLatticeInSpan_discrete G

attribute [local instance] Lie.MixedLattice.Construction.lieMixedLatticeInSpan_isZLattice

theorem anisotropic_integral_faithful_uniform_gap
    {k : Type} [Field k] [NumberField k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (haniso : Algebraic.IsAnisotropic G) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G.matrixGroup,
      ∀ x : Fin G.dimension → 𝓞 k, x ≠ 0 →
        ε ≤ ‖(Archimedean.LieMem.Construction.archimedeanLieUnit G.matrixGroup g).val.mulVec
          (fun i => mixedEmbedding k (x i : k))‖ := by
  obtain ⟨b, K, hK, hrep⟩ := AdjointMahlerRepresentatives.Construction.anisotropic_adjoint_compact_lattice_representatives G haniso
  obtain ⟨ε, hε, hgap⟩ := AdjointFaithfulGap.Construction.integral_faithful_gap_of_adjoint_representatives
    G.matrixGroup G.connected G.semisimple b K hK Set.univ (fun g _ => hrep g)
  exact ⟨ε, hε, fun g => hgap g (Set.mem_univ g)⟩

theorem anisotropic_faithful_minkowski_uniform_gap
    {k : Type} [Field k] [NumberField k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (haniso : Algebraic.IsAnisotropic G) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : G.matrixGroup.ArchimedeanProduct Set.univ,
      ∀ x ∈ IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k G.dimension).module, x ≠ 0 →
        ε ≤ ‖Archimedean.Quotient.Construction.archimedeanRealRepresentation k G.dimension
          (Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G.matrixGroup g).val x‖ := by
  obtain ⟨ε, hε, hgap⟩ := anisotropic_integral_faithful_uniform_gap G haniso
  refine ⟨ε, hε, fun g x hx hx0 => ?_⟩
  rw [Minkowski.IntegralAction.Construction.standard_vectorLatticeImage_eq_pi] at hx
  choose a ha using fun i => hx i (Set.mem_univ i)
  have he : (fun i => mixedEmbedding k (a i : k)) = x := funext ha
  have ha0 : a ≠ 0 := by
    intro h
    apply hx0
    rw [← he, h]
    simp
    rfl
  have h := hgap (Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G.matrixGroup g) a ha0
  rw [he] at h
  exact h

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.AnisotropicFaithfulGap.Construction
