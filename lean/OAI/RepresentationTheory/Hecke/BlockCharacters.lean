import OAI.AlgebraicGeometry.PELModuli.CMPoints.Arithmetic
import OAI.RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents

/-! # Block Characters -/

namespace OAI.RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic

noncomputable section

/-! The coefficient character of a split level-one block and a nonzero
additive character of its literal finite label group. -/

variable {k : Type} [Field k] {q : ℕ} [CharP k q]

def blockResidueCast : ZMod (q ^ 1) →+* k := ZMod.castHom (by simp) k

def blockTangentCharacter {d : ℕ} (v : Fin d) :
    Additive (ULift (Multiplicative (Fin d → ZMod (q ^ 1)))) →+ k where
  toFun a := blockResidueCast (a.toMul.down.toAdd v)
  map_zero' := map_zero blockResidueCast
  map_add' a b := map_add blockResidueCast (a.toMul.down.toAdd v) (b.toMul.down.toAdd v)

theorem blockTangentCharacter_ne_zero {d : ℕ} (v : Fin d) :
    blockTangentCharacter (k := k) (q := q) v ≠ 0 := by
  intro h
  have he := congrArg (fun f :
      Additive (ULift (Multiplicative (Fin d → ZMod (q ^ 1)))) →+ k =>
        f (Additive.ofMul (ULift.up (Multiplicative.ofAdd (fun _ => 1))))) h
  change blockResidueCast (1 : ZMod (q ^ 1)) = 0 at he
  exact one_ne_zero ((map_one blockResidueCast).symm.trans he)

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} [Fact q.Prime]
  (j : AlgebraicGeometry.PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (τ : Gal(E/ℚ))

def blockLieCharacter : NumberField.RingOfIntegers E →+* k :=
  blockResidueCast.comp (j.residueCharacter iota τ 1)

theorem blockLieCharacter_nat (a : NumberField.RingOfIntegers E) :
    blockLieCharacter (k := k) j iota τ a =
      ((j.residueCharacter iota τ 1 a).val : k) := by
  let z := j.residueCharacter iota τ 1 a
  exact ((map_natCast (blockResidueCast (k := k) (q := q)) z.val).symm.trans
    (congrArg (blockResidueCast (k := k) (q := q)) (ZMod.natCast_zmod_val z))).symm

theorem blockLieCharacter_projector (hsplit : j.HasSplitCoordinates iota) :
    blockLieCharacter (k := k) j iota τ (j.projector iota hsplit 1 τ) = 1 := by
  classical
  have hc : j.residueCharacter iota τ 1 (j.projector iota hsplit 1 τ) = 1 := by
    have h := congrFun (j.projector_coordinates iota hsplit 1 τ) τ
    exact h.trans (Pi.single_eq_same _ _)
  exact (congrArg (blockResidueCast (k := k) (q := q)) hc).trans (map_one _)

end

end OAI.RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic
