import OAI.NumberTheory.ArithmeticGroups.Lattices.KillingOrderStabilizerLattice
import OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.BracketOperatorEquiv

/-! # Bracket Integral Lattice -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.BracketIntegralLattice.Construction

noncomputable section

/-! The actual Minkowski Lie order has a lattice of integral automorphisms. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

local instance lieMixedSpan_normed_uniform_for_integral_lattice
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    UniformSpace (MixedLattice.Construction.lieMixedSpan G) :=
  (inferInstance : NormedAddCommGroup (MixedLattice.Construction.lieMixedSpan G)).toUniformSpace

local instance lieMixedSpan_normed_topology_for_integral_lattice
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    TopologicalSpace (MixedLattice.Construction.lieMixedSpan G) :=
  (inferInstance : NormedAddCommGroup (MixedLattice.Construction.lieMixedSpan G)).toUniformSpace.toTopologicalSpace

theorem lieBracket_integral_stabilizer_isLattice
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    (b : Module.Basis (Fin m) ℝ (MixedLattice.Construction.lieMixedSpan G)) :
    IntegralLattice.IsLattice ((SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b)
      (MixedLattice.Construction.lieMixedLatticeInSpan G)).subgroupOf (BracketStabilizer.Construction.lieBracketMatrixGroup G hG b)) := by
  let Λ := MixedLattice.Construction.lieMixedLatticeInSpan G
  let B := Minkowski.LieTangent.Construction.lieMixedContinuousBracket G hG
  let : DiscreteTopology Λ := MixedLattice.Construction.lieMixedLatticeInSpan_discrete G
  let : IsZLattice ℝ Λ := MixedLattice.Construction.lieMixedLatticeInSpan_isZLattice G
  have hl := KillingOrderStabilizerLattice.Construction.killing_order_stabilizer_isLattice Λ B
    (MinkowskiSelfAdjointRealization.Construction.lieMixedContinuousBracket_isLie G hG) (MinkowskiSelfAdjointRealization.Construction.lieMixedContinuousBracket_killing_nondegenerate G hG hsemi)
    (fun x hx y hy => Minkowski.LieBracket.Construction.lieMixedBracket_integral G hG x y hx hy)
  let e := BracketOperatorEquiv.Construction.lieBracketOperatorEquiv G hG b
  let f := e.toMonoidHom
  let : Subsingleton f.ker := ⟨fun x y => Subtype.ext (e.injective (x.property.trans y.property.symm))⟩
  let : Finite f.ker := inferInstance
  have ht := LatticeEquivTransport.Construction.lattice_comap_of_open_surjective_finite_kernel f e.surjective e.continuous e.isOpenMap _ hl
  have he : (Bracket.OrderStabilizer.Construction.bracketOrderStabilizer B Λ).comap f =
      (SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b) Λ).subgroupOf (BracketStabilizer.Construction.lieBracketMatrixGroup G hG b) := by
    ext g
    change e g ∈ Bracket.OrderStabilizer.Construction.bracketOrderStabilizer B Λ ↔ g.val ∈ SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b) Λ
    rw [Bracket.OrderStabilizer.Construction.mem_bracketOrderStabilizer_iff, StabilizerRestriction.Construction.submoduleImageStabilizer_mem_iff]
    exact forall_congr' (fun x => by
      change ((BracketOperatorEquiv.Construction.lieBracketOperatorEquiv G hG b g).val.val x ∈ Λ ↔ x ∈ Λ) ↔ _
      rw [BracketOperatorEquiv.Construction.lieBracketOperatorEquiv_apply]
      rfl)
  rwa [he] at ht

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.BracketIntegralLattice.Construction
