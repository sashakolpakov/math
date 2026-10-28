import OAI.RepresentationTheory.Hecke.BlockCharacters
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockTangentCoordinates

/-! # Block Lie Character -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockLieCharacter.CM

noncomputable section

/-! The original Lie character is the residue of the same integral
coefficient character at every positive torsion level. -/

variable {k E K : Type} [Field k] [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime] [CharP k q]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (τ : Gal(E/ℚ))

theorem character_eq (n : ℕ) : RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter (k := k) j iota τ =
    (BlockTangentCoordinates.CM.residueCast k q n).comp (j.residueCharacter iota τ (n + 1)) := by
  have hc := j.residueCharacter_compatible iota τ 1 (n + 1) (Nat.le_add_left 1 n)
  have he : (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockResidueCast (k := k) (q := q)).comp
      (ZMod.castHom (pow_dvd_pow q (Nat.le_add_left 1 n)) (ZMod (q ^ 1))) =
      BlockTangentCoordinates.CM.residueCast k q n := Subsingleton.elim _ _
  change (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockResidueCast (k := k) (q := q)).comp
    (j.residueCharacter iota τ 1) = _
  rw [← hc, ← RingHom.comp_assoc, he]

theorem character_nat (n : ℕ) (a : NumberField.RingOfIntegers E) :
    RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter (k := k) j iota τ a =
      ((j.residueCharacter iota τ (n + 1) a).val : k) := by
  rw [character_eq j iota τ n]
  let z := j.residueCharacter iota τ (n + 1) a
  exact ((map_natCast (BlockTangentCoordinates.CM.residueCast k q n) z.val).symm.trans
    (congrArg (BlockTangentCoordinates.CM.residueCast k q n) (ZMod.natCast_zmod_val z))).symm

theorem character_projector (hsplit : j.HasSplitCoordinates iota) (n : ℕ) :
    RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter (k := k) j iota τ (j.projector iota hsplit (n + 1) τ) = 1 := by
  classical
  rw [character_eq j iota τ n]
  change BlockTangentCoordinates.CM.residueCast k q n
    (j.residueCharacter iota τ (n + 1) (j.projector iota hsplit (n + 1) τ)) = 1
  have hc := congrFun (j.projector_coordinates iota hsplit (n + 1) τ) τ
  have hc' : j.residueCharacter iota τ (n + 1) (j.projector iota hsplit (n + 1) τ) = 1 :=
    hc.trans (Pi.single_eq_same _ _)
  exact (congrArg (BlockTangentCoordinates.CM.residueCast k q n) hc').trans (map_one _)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockLieCharacter.CM
