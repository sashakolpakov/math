import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ReducedCanonicalAdjoints
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsSheafKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PerfectBlocks
import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockDecomposition

/-! # Reduced Coefficient Perfection -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ReducedCoefficientPerfection

noncomputable section

/-! The actual conjugate coefficient blocks have perfect canonical
pairings over a reduced locally Noetherian base. This applies integrally
at q as well as to the original generic source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ReducedCanonicalAdjoints

variable {S : Scheme} [IsReduced S] [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
  {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)

omit [IsReduced S] [IsLocallyNoetherian S] [NumberField.IsCMField E] in
theorem reduced_native_projector_idempotent (n : ℕ) (τ : Gal(E/ℚ)) :
    AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap (q ^ n) (ρ.map (j.projector iota hsplit n τ)) ≫
      AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap (q ^ n) (ρ.map (j.projector iota hsplit n τ)) =
      AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap (q ^ n) (ρ.map (j.projector iota hsplit n τ)) := by
  have h := PELModuli.CMPoints.BlockDecomposition.projector_idempotent_on_torsion j iota hsplit A.abelian ρ n τ
    (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.abelian.scheme (q ^ n))
    (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.abelian.scheme (q ^ n))
    (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion_killed A.abelian.scheme (q ^ n))
  apply (cancel_mono (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.abelian.scheme (q ^ n))).mp
  rw [Category.assoc, AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap_inclusion, ← Category.assoc, AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap_inclusion]
  exact h

def reducedCanonicalCoefficientPairing (n : ℕ) (τ υ : Gal(E/ℚ)) :
    AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter
      (A := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (ρ.map (j.projector iota hsplit n τ)))
      (B := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (ρ.map (j.projector iota hsplit n υ)))
      (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) :=
  (AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing A.abelian A.dual A.polarization
    (q ^ n) (pow_pos (Fact.out : q.Prime).pos n)).restrict
    (AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointInclusion (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap (q ^ n) (ρ.map (j.projector iota hsplit n τ))))
    (AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointInclusion (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap (q ^ n) (ρ.map (j.projector iota hsplit n υ))))

theorem reducedCanonicalCoefficientPairing_isPerfect (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ)
    (hdegree : q.Coprime (∏ i, δ i)) (n : ℕ) (τ υ : Gal(E/ℚ))
    (hυ : υ = PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ) :
    (reducedCanonicalCoefficientPairing j iota hsplit A ρ n τ υ).toSheafPairing.IsPerfect := by
  apply AbelianScheme.IsogenyQuotient.PerfectBlocks.Construction.fixedPointPairing_isPerfect
    (AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing A.abelian A.dual A.polarization
      (q ^ n) (pow_pos (Fact.out : q.Prime).pos n))
    (AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing_isPerfect A.abelian A.dual A.polarization
      (q ^ n) _ ((hdegree.pow_left n).pow_right 2))
    _ _ (reduced_native_projector_idempotent j iota hsplit A ρ n τ)
    (reduced_native_projector_idempotent j iota hsplit A ρ n υ)
  intro T x y
  rw [hυ]
  exact AbelianScheme.IsogenyQuotient.ProjectorAdjoints.Construction.l45_projectors_adjoint_of_integral_action j iota hsplit A.abelian ρ n
    (AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing A.abelian A.dual A.polarization (q ^ n)
      (pow_pos (Fact.out : q.Prime).pos n))
    (ReducedCanonicalAdjoints.reducedNativePolarizationPairing_coefficient_adjoint A ρ hρ (q ^ n) _) τ T x y

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ReducedCoefficientPerfection
