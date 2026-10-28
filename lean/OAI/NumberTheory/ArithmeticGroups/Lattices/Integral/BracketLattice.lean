import OAI.NumberTheory.ArithmeticGroups.Lattices.ConjugatedIntegralBracketLattice
import OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.UnitConjugationEquiv
import OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeEquivTransport
import OAI.NumberTheory.ArithmeticGroups.Lattices.SelfAdjointBracketRealization

/-! # Bracket Lattice -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.BracketLattice.Construction

noncomputable section

/-! Integral automorphisms of any real Killing Lie bracket form a lattice. -/

open scoped OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.UnitAction.Construction.BracketAction

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

def integralBracketSubgroup {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (B : L →L[ℝ] L →L[ℝ] L) (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) :
    Subgroup (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) :=
  (VolumeOperatorSiegelCover.Construction.ambientIntegralOperatorGroup b).comap (Bracket.ConjugationAction.Construction.bracketVolumeHom B hK)

theorem integralBracketSubgroup_isLattice {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (hint : Bilinear.DiagonalCoordinates.Construction.continuousBilinearCoordinates b.toBasis B ∈ RealCoordinates.Construction.integralRealCoordinates (Fin m × Fin m × Fin m)) :
    IntegralLattice.IsLattice (integralBracketSubgroup b B hK) := by
  obtain ⟨a, haB, haK, hadj⟩ := SelfAdjointBracketRealization.Construction.exists_volume_selfAdjoint_bracket_realization B hB hK
  let e := Bracket.UnitConjugationEquiv.Construction.bracketUnitConjugationEquiv B a.val
  let f := e.toMonoidHom
  let : Subsingleton f.ker := ⟨fun x y => Subtype.ext (e.injective (x.property.trans y.property.symm))⟩
  let : Finite f.ker := inferInstance
  have hl := LatticeEquivTransport.Construction.lattice_comap_of_open_surjective_finite_kernel f e.surjective e.continuous e.isOpenMap
    (Bracket.ConjugationAction.Construction.conjugatedIntegralBracketSubgroup b (a • B) haK a)
    (ConjugatedIntegralBracketLattice.Construction.conjugatedIntegralBracketSubgroup_isLattice b B hint a haB haK hadj)
  have he : (Bracket.ConjugationAction.Construction.conjugatedIntegralBracketSubgroup b (a • B) haK a).comap f =
      integralBracketSubgroup b B hK := by
    ext g
    change Bracket.ConjugationAction.Construction.conjugatedBracketVolumeHom (a • B) haK a (e g) ∈ VolumeOperatorSiegelCover.Construction.ambientIntegralOperatorGroup b ↔
      Bracket.ConjugationAction.Construction.bracketVolumeHom B hK g ∈ VolumeOperatorSiegelCover.Construction.ambientIntegralOperatorGroup b
    have hv : Bracket.ConjugationAction.Construction.conjugatedBracketVolumeHom (a • B) haK a (e g) = Bracket.ConjugationAction.Construction.bracketVolumeHom B hK g := by
      apply Subtype.ext
      change a.val⁻¹ * (a.val * g.val * a.val⁻¹) * a.val = g.val
      group
    rw [hv]
  rwa [he] at hl

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.BracketLattice.Construction
