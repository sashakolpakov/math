import OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.OrderBases
import OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointMahlerRepresentatives

/-! # Order Frame -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.OrderFrame.Construction

noncomputable section

/-! Integral changes of Lie-lattice basis give spanning families of
rational Lie matrices with the expected Minkowski frame coordinates. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding _root_.Module

attribute [local instance] LieRing.ofAssociativeRing

theorem lieOrder_basis_spans_matrices
    {k ι : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (b : Basis ι ℤ (Integral.Lie.Construction.integralLieOrder G))
    (T : Matrix (Fin n) (Fin n) k) (hT : T ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    T ∈ Submodule.span k (Set.range (fun i => (b i).val.val)) := by
  let W := Submodule.span k (Set.range (fun i => (b i).val.val))
  let V := (W.restrictScalars ℚ).comap
    ((Infinitesimal.Action.Construction.infinitesimalStabilizer G).toSubmodule.subtype.restrictScalars ℚ)
  have hV : (⊤ : Submodule ℚ (Infinitesimal.Action.Construction.infinitesimalStabilizer G)) ≤ V := by
    rw [← (OrderBases.Construction.lieOrderRationalBasis G b).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (OrderBases.Construction.lieOrderRationalBasis G b i).val ∈ W
    rw [OrderBases.Construction.lieOrderRationalBasis_apply]
    exact Submodule.subset_span ⟨i, rfl⟩
  exact hV (Submodule.mem_top : (⟨T, hT⟩ : Infinitesimal.Action.Construction.infinitesimalStabilizer G) ∈ ⊤)

local instance lieOrderFrame_normed_discrete
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    @DiscreteTopology (MixedLattice.Construction.lieMixedLatticeInSpan G)
      (@instTopologicalSpaceSubtype (MixedLattice.Construction.lieMixedSpan G) _
        (inferInstance : NormedAddCommGroup (MixedLattice.Construction.lieMixedSpan G)).toUniformSpace.toTopologicalSpace) :=
  MixedLattice.Construction.lieMixedLatticeInSpan_discrete G

attribute [local instance] MixedLattice.Construction.lieMixedLatticeInSpan_isZLattice

theorem exists_integral_lie_basis_of_frame_change
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n)
    (b : Basis (Fin m) ℤ (MixedLattice.Construction.lieMixedLatticeInSpan G))
    (γ : Matrix.GeneralLinearGroup (Fin m) ℝ)
    (hγ : γ ∈ SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction (b.ofZLatticeBasis ℝ))
      (MixedLattice.Construction.lieMixedLatticeInSpan G)) :
    ∃ c : Basis (Fin m) ℤ (Integral.Lie.Construction.integralLieOrder G), ∀ i,
      ((c i).val.val).map (mixedEmbedding k) =
        (LatticeFrameAction.Construction.matrixFrameAction (b.ofZLatticeBasis ℝ) γ ((b.ofZLatticeBasis ℝ) i)).val := by
  let e := StabilizerRestriction.Construction.stabilizerRestriction (LatticeFrameAction.Construction.matrixFrameIntegralAction (b.ofZLatticeBasis ℝ))
    (MixedLattice.Construction.lieMixedLatticeInSpan G) ⟨γ, hγ⟩
  let c := b.map (e.trans (OrderBases.Construction.integralLieOrderMixedEquiv G).symm)
  refine ⟨c, fun i => ?_⟩
  have he : OrderBases.Construction.integralLieOrderMixedEquiv G (c i) = e (b i) := by
    simp only [c, Basis.map_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  have hm := congrArg (fun y : MixedLattice.Construction.lieMixedLatticeInSpan G => y.val.val) he
  rw [Basis.ofZLatticeBasis_apply]
  exact hm

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.OrderFrame.Construction
