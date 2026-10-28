import OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.ExteriorAction

/-! # Integral Discrete -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.IntegralDiscrete.Construction

noncomputable section

/-! The ambient integral special-linear subgroup is discrete in the
product of all archimedean groups. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

theorem fullArchimedeanIntegralSL_discrete
    (k : Type) [Field k] [NumberField k] (n : ℕ) :
    DiscreteTopology (ExteriorAction.Construction.fullArchimedeanIntegralSL k n) := by
  let Λ := Integral.Matrices.Construction.integralCoordinateLattice (R := 𝓞 k) (k := k) n
  have hfg : Λ.FG := by
    change (Integral.Matrices.Construction.integralCoordinateLattice (R := 𝓞 k) (k := k) n).FG
    rw [Integral.Matrices.Construction.integralCoordinateLattice_eq_span]
    exact Submodule.fg_span (Set.finite_range _)
  let L := AdeleCoordinateLattice.Construction.coordinateAdeleLattice Λ
  let : DiscreteTopology L := AdeleCoordinateLattice.Construction.coordinateAdeleLattice_discrete Λ hfg
  let f : ExteriorAction.Construction.fullArchimedeanIntegralSL k n → Fin n → L := fun g j =>
    ⟨fun v i => g.val v i j, by
      obtain ⟨A, hA⟩ := g.property
      refine ⟨fun i => algebraMap (𝓞 k) k (A i j), ?_, ?_⟩
      · exact (Integral.Matrices.Construction.mem_integralCoordinateLattice _).mpr (fun i => ⟨A i j, rfl⟩)
      · funext v i
        exact congrArg (fun z : ExteriorAction.Construction.FullArchimedeanSL k n => z v i j) hA⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · apply continuous_pi
    intro j
    apply Continuous.subtype_mk
    apply continuous_pi
    intro v
    apply continuous_pi
    intro i
    exact (continuous_apply j).comp (Matrix.SpecialLinearGroup.continuous_apply _
      ((continuous_apply v).comp continuous_subtype_val) i)
  · intro g h he
    apply Subtype.ext
    funext v
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact congrArg (fun z : Fin n → L => (z j).val v i) he

instance fullArchimedeanSL_locallyCompact
    (k : Type) [Field k] [NumberField k] (n : ℕ) : LocallyCompactSpace (ExteriorAction.Construction.FullArchimedeanSL k n) := by
  let : ∀ v : InfinitePlace k, LocallyCompactSpace (Algebraic.SL n v.Completion) := fun v => by
    let : LocallyCompactSpace (Matrix (Fin n) (Fin n) v.Completion) :=
      inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → v.Completion))
    exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace
  exact Pi.locallyCompactSpace_of_finite

instance fullArchimedeanSL_secondCountable
    (k : Type) [Field k] [NumberField k] (n : ℕ) : SecondCountableTopology (ExteriorAction.Construction.FullArchimedeanSL k n) := by
  let : ∀ v : InfinitePlace k, SecondCountableTopology (Algebraic.SL n v.Completion) := fun v => by
    let : SecondCountableTopology v.Completion :=
      (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
    let : SecondCountableTopology (Matrix (Fin n) (Fin n) v.Completion) :=
      inferInstanceAs (SecondCountableTopology (Fin n → Fin n → v.Completion))
    exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology ((v : InfinitePlace k) → Algebraic.SL n v.Completion))

theorem fullArchimedeanMatrixGroup_closed
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    IsClosed (ExteriorAction.Construction.fullArchimedeanMatrixGroup G : Set (ExteriorAction.Construction.FullArchimedeanSL k n)) := by
  have he : (ExteriorAction.Construction.fullArchimedeanMatrixGroup G : Set (ExteriorAction.Construction.FullArchimedeanSL k n)) =
      ⋂ v, (fun g : ExteriorAction.Construction.FullArchimedeanSL k n => g v) ⁻¹'
        (G.subgroup v.Completion (algebraMap k v.Completion) : Set (Algebraic.SL n v.Completion)) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [he]
  exact isClosed_iInter (fun v => (G.subgroup_isClosed (algebraMap k v.Completion)).preimage
    (continuous_apply v))

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.IntegralDiscrete.Construction
