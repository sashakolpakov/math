import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.Labels
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum

/-! # Conjugate Projectors -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ConjugateProjectors.Construction

noncomputable section

/-!
Complex conjugation carries each integral residue projector to the
conjugate projector modulo q^n. Consequently their actions agree on the
actual native torsion scheme; no equality of the integral lifts is assumed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]

theorem cmConjugation_central (τ : Gal(E/ℚ)) :
    τ * PELModuli.CMPoints.Arithmetic.rationalConjugation E = PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ := by
  let φ : E →+* ℂ := Classical.choice (inferInstance : Nonempty (E →+* ℂ))
  ext x
  apply φ.injective
  exact (NumberField.IsCMField.complexEmbedding_complexConj E (φ.comp τ.toRingHom) x).trans
    (NumberField.IsCMField.complexEmbedding_complexConj E φ (τ x)).symm

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)

theorem l45_residueCharacter_conjugate (n : ℕ) (τ : Gal(E/ℚ))
    (a : NumberField.RingOfIntegers E) :
    j.residueCharacter iota τ n (NumberField.IsCMField.ringOfIntegersComplexConj E a) =
      j.residueCharacter iota (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ) n a := by
  apply congrArg (PadicInt.toZModPow n)
  apply congrArg j.integralEmbedding
  apply NumberField.RingOfIntegers.ext
  change iota (τ (NumberField.IsCMField.complexConj E (a : E))) =
    iota (NumberField.IsCMField.complexConj E (τ (a : E)))
  exact congrArg iota (congrArg (fun (automorphism : Gal(E/ℚ)) => automorphism (a : E)) (cmConjugation_central τ))

variable (hsplit : j.HasSplitCoordinates iota)

theorem l45_projector_conjugate_congruence (n : ℕ) (τ : Gal(E/ℚ)) :
    NumberField.IsCMField.ringOfIntegersComplexConj E (j.projector iota hsplit n τ) -
      j.projector iota hsplit n (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ) ∈
        Ideal.span ({(q ^ n : NumberField.RingOfIntegers E)} : Set (NumberField.RingOfIntegers E)) := by
  classical
  have hc (υ : Gal(E/ℚ)) :
      PELModuli.CMPoints.Arithmetic.rationalConjugation E * υ = τ ↔ υ = PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ := by
    constructor
    · intro h
      have hh := congrArg (fun z => PELModuli.CMPoints.Arithmetic.rationalConjugation E * z) h
      exact (CM.Labels.Construction.cmConjugation_involutive υ).symm.trans hh
    · intro h
      rw [h]
      exact CM.Labels.Construction.cmConjugation_involutive τ
  have he : j.residueCoordinates iota n
      (NumberField.IsCMField.ringOfIntegersComplexConj E (j.projector iota hsplit n τ)) =
        j.residueCoordinates iota n (j.projector iota hsplit n (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ)) := by
    ext υ
    change j.residueCharacter iota υ n _ = j.residueCharacter iota υ n _
    rw [l45_residueCharacter_conjugate]
    have hleft := congrFun (j.projector_coordinates iota hsplit n τ) (PELModuli.CMPoints.Arithmetic.rationalConjugation E * υ)
    have hright := congrFun (j.projector_coordinates iota hsplit n (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ)) υ
    change j.residueCharacter iota (PELModuli.CMPoints.Arithmetic.rationalConjugation E * υ) n _ = _ at hleft
    change j.residueCharacter iota υ n _ = _ at hright
    rw [hleft, hright]
    simp only [Pi.single_apply, hc]
  rw [← (hsplit n).2]
  change j.residueCoordinates iota n (_ - _) = 0
  rw [map_sub, he, sub_self]

theorem l45_native_projector_conjugate
    {S : Scheme} {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S)
    (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A) (n : ℕ) (τ : Gal(E/ℚ)) :
    Torsion.Groups.Construction.nativeTorsionMap (q ^ n) (σ.map
      (NumberField.IsCMField.ringOfIntegersComplexConj E (j.projector iota hsplit n τ))) =
        Torsion.Groups.Construction.nativeTorsionMap (q ^ n) (σ.map
          (j.projector iota hsplit n (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ))) := by
  have hh := PELModuli.CMPoints.BlocksProjectors.action_eq_of_congruence A σ _ _ (q ^ n)
    (by simpa only [Nat.cast_pow] using l45_projector_conjugate_congruence j iota hsplit n τ)
    (Torsion.Groups.Construction.nativeTorsionScheme A.scheme (q ^ n)) (Torsion.Groups.Construction.nativeTorsionInclusion A.scheme (q ^ n))
    (Torsion.Groups.Construction.nativeTorsionInclusion_killed A.scheme (q ^ n))
  apply (cancel_mono (Torsion.Groups.Construction.nativeTorsionInclusion A.scheme (q ^ n))).mp
  rw [Torsion.Groups.Construction.nativeTorsionMap_inclusion, Torsion.Groups.Construction.nativeTorsionMap_inclusion]
  exact hh

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ConjugateProjectors.Construction
