import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.PairingValues
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SourcePolarizationAdjoints
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsSheafKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PerfectBlocks

/-! # Coefficient Perfection -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.CoefficientPerfection

noncomputable section

/-! Perfection of the actual canonical pairing on conjugate coefficient
blocks follows from the source polarization, its Rosati condition, and
the original CMPoints projectors. No block pairing is supplied as data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SourcePolarizationAdjoints.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.PairingValues

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)

omit [Algebra ℚ E] in
theorem canonical_native_coefficient_adjoint (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ)
    (m : ℕ) (hm : 0 < m) (a : NumberField.RingOfIntegers E)
    (T : Over (Spec (.of k))) (x y : T ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.abelian.scheme m) :
    (PairingValues.prescribedNativePairing A m hm).pairValue (x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap m (ρ.map a)) y =
      (PairingValues.prescribedNativePairing A m hm).pairValue x
        (y ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap m (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a))) :=
  AbelianScheme.IsogenyQuotient.CM.PointsSheafKernel.Construction.integralTorsionSheafPairing_adjoint A.abelian ρ m (AbelianScheme.FrobeniusKernel.CartierDualityCanonical.Construction.e56SourceTorsionPairing A m hm) a
    (NumberField.IsCMField.ringOfIntegersComplexConj E a)
    (AbelianScheme.FrobeniusKernel.SourcePolarizationAdjoints.Construction.sourceCanonicalPairing_coefficient_adjoint A ρ hρ m hm a) T x y

omit [IsAlgClosed k] [NumberField.IsCMField E] in
theorem native_coefficient_projector_idempotent (n : ℕ) (τ : Gal(E/ℚ)) :
    AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap (q ^ n) (ρ.map (j.projector iota hsplit n τ)) ≫
      AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap (q ^ n) (ρ.map (j.projector iota hsplit n τ)) =
      AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap (q ^ n) (ρ.map (j.projector iota hsplit n τ)) := by
  have h := PELModuli.CMPoints.BlockDecomposition.projector_idempotent_on_torsion j iota hsplit A.abelian ρ n τ
    (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.abelian.scheme (q ^ n))
    (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.abelian.scheme (q ^ n))
    (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion_killed A.abelian.scheme (q ^ n))
  apply (cancel_mono (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.abelian.scheme (q ^ n))).mp
  rw [Category.assoc, AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap_inclusion, ← Category.assoc,
    AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap_inclusion]
  exact h

def canonicalCoefficientPairing (n : ℕ) (τ υ : Gal(E/ℚ)) :
    AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter
      (A := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (ρ.map (j.projector iota hsplit n τ)))
      (B := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (ρ.map (j.projector iota hsplit n υ)))
      (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X) :=
  (PairingValues.prescribedNativePairing A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n)).restrict
    (AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointInclusion (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap (q ^ n) (ρ.map (j.projector iota hsplit n τ))))
    (AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointInclusion (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap (q ^ n) (ρ.map (j.projector iota hsplit n υ))))

theorem canonicalCoefficientPairing_isPerfect (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ)
    (hdegree : q.Coprime (∏ i, δ i)) (n : ℕ) (τ υ : Gal(E/ℚ))
    (hυ : υ = PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ) :
    (canonicalCoefficientPairing j iota hsplit A ρ n τ υ).toSheafPairing.IsPerfect := by
  apply AbelianScheme.IsogenyQuotient.PerfectBlocks.Construction.fixedPointPairing_isPerfect
    (PairingValues.prescribedNativePairing A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n))
    (PairingValues.prescribedNativePairing_isPerfect A (q ^ n) _ (hdegree.pow_left n))
    _ _ (native_coefficient_projector_idempotent j iota hsplit A ρ n τ)
    (native_coefficient_projector_idempotent j iota hsplit A ρ n υ)
  intro T x y
  rw [hυ]
  exact AbelianScheme.IsogenyQuotient.ProjectorAdjoints.Construction.l45_projectors_adjoint_of_integral_action j iota hsplit A.abelian ρ n
    (PairingValues.prescribedNativePairing A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n))
    (canonical_native_coefficient_adjoint A ρ hρ (q ^ n) _) τ T x y

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.CoefficientPerfection
