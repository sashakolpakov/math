import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.BasisRational
import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.AdjointOperator

/-! # Order Bases -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.OrderBases.Construction

noncomputable section

/-! Compatible integral, rational, and real bases of the Lie order
and its Minkowski span. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding _root_.Module

def integralLieOrderMixedMap
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    Integral.Lie.Construction.integralLieOrder G →ₗ[ℤ] MixedLattice.Construction.lieMixedLatticeInSpan G where
  toFun A := ⟨Archimedean.Lie.Construction.lieMixedSpanRationalMap G A.val, ⟨A.val, A.property, rfl⟩⟩
  map_add' A B := Subtype.ext ((Archimedean.Lie.Construction.lieMixedSpanRationalMap G).map_add A.val B.val)
  map_smul' r A := Subtype.ext (((Archimedean.Lie.Construction.lieMixedSpanRationalMap G).restrictScalars ℤ).map_smul r A.val)

theorem integralLieOrderMixedMap_bijective
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    Function.Bijective (integralLieOrderMixedMap G) := by
  constructor
  · intro A B h
    apply Subtype.ext
    apply Minkowski.AdjointOperator.Construction.lieMixedSpanRationalMap_injective G
    exact congrArg (fun x : MixedLattice.Construction.lieMixedLatticeInSpan G => x.val) h
  · intro x
    obtain ⟨A, hA, he⟩ := x.property
    refine ⟨⟨A, hA⟩, ?_⟩
    apply Subtype.ext
    exact Subtype.ext he

def integralLieOrderMixedEquiv
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    Integral.Lie.Construction.integralLieOrder G ≃ₗ[ℤ] MixedLattice.Construction.lieMixedLatticeInSpan G :=
  LinearEquiv.ofBijective (integralLieOrderMixedMap G) (integralLieOrderMixedMap_bijective G)

def lieOrderRationalBasis
    {k ι : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (b : Basis ι ℤ (Integral.Lie.Construction.integralLieOrder G)) :
    Basis ι ℚ (Infinitesimal.Action.Construction.infinitesimalStabilizer G) :=
  Integral.BasisRational.Construction.rationalBasisOfIntegralBasis (Integral.Lie.Construction.integralLieOrder G).toSubmodule (MixedLattice.Construction.integralLieLattice_full_rational G) b

theorem lieOrderRationalBasis_apply
    {k ι : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (b : Basis ι ℤ (Integral.Lie.Construction.integralLieOrder G)) (i : ι) :
    lieOrderRationalBasis G b i = (b i).val :=
  Integral.BasisRational.Construction.rationalBasisOfIntegralBasis_apply _ _ b i

local instance lieMixedLatticeInSpan_normed_discrete_for_basis
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    @DiscreteTopology (MixedLattice.Construction.lieMixedLatticeInSpan G)
      (@instTopologicalSpaceSubtype (MixedLattice.Construction.lieMixedSpan G) _
        (inferInstance : NormedAddCommGroup (MixedLattice.Construction.lieMixedSpan G)).toUniformSpace.toTopologicalSpace) :=
  MixedLattice.Construction.lieMixedLatticeInSpan_discrete G

attribute [local instance] MixedLattice.Construction.lieMixedLatticeInSpan_isZLattice

def lieOrderRealBasis
    {k ι : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (b : Basis ι ℤ (Integral.Lie.Construction.integralLieOrder G)) : Basis ι ℝ (MixedLattice.Construction.lieMixedSpan G) :=
  (b.map (integralLieOrderMixedEquiv G)).ofZLatticeBasis ℝ

theorem lieOrderRealBasis_apply
    {k ι : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (b : Basis ι ℤ (Integral.Lie.Construction.integralLieOrder G)) (i : ι) :
    lieOrderRealBasis G b i = Archimedean.Lie.Construction.lieMixedSpanRationalMap G (lieOrderRationalBasis G b i) := by
  rw [lieOrderRealBasis, Basis.ofZLatticeBasis_apply, Basis.map_apply, lieOrderRationalBasis_apply]
  rfl

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.OrderBases.Construction
