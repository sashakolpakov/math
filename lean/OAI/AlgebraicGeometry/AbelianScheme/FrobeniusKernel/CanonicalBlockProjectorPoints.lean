import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalBlockComponents
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePointBicharacter

/-! # Canonical Block Projector Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalBlockProjectorPoints.Construction

noncomputable section

/-! The native block points have exactly their original coefficient
support, and the canonical pairing is trivial on a zero argument. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))

theorem canonicalTorsionOrthogonal_one_left (m : ℕ) (hm : 0 < m)
    (T : Over (Spec (.of k))) (y : (A.abelian.torsionFunctor m).obj (.op T)) :
    Prescription.Construction.canonicalTorsionOrthogonal A m hm T 1 y := by
  apply (DualityIntrinsicPointValues.Construction.canonicalTorsionOrthogonal_iff_value A m hm T 1 y).mpr
  exact (ReferencePointBicharacter.Construction.originalPointBicharacter_value A m hm T 1 y).symm.trans
    (congrArg (fun f => f y) (ReferencePointBicharacter.Construction.originalPointBicharacter A m hm T).map_one)

theorem canonicalTorsionOrthogonal_one_right (m : ℕ) (hm : 0 < m)
    (T : Over (Spec (.of k))) (x : (A.abelian.torsionFunctor m).obj (.op T)) :
    Prescription.Construction.canonicalTorsionOrthogonal A m hm T x 1 := by
  apply (DualityIntrinsicPointValues.Construction.canonicalTorsionOrthogonal_iff_value A m hm T x 1).mpr
  exact (ReferencePointBicharacter.Construction.originalPointBicharacter_value A m hm T x 1).symm.trans
    (ReferencePointBicharacter.Construction.originalPointBicharacter A m hm T x).map_one

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
  (n : ℕ) (τ : Gal(E/ℚ)) (T : Over (Spec (.of k)))
  (x : T ⟶ (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n).X)

omit [IsAlgClosed k] in
theorem canonicalOriginalBlockPoint_one :
    CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n τ T 1 = 1 :=
  (congrArg ((PELModuli.CMPoints.BlocksProjectors.blockInclusion A.abelian ρ (j.localCharacter iota τ) n).app (.op T))
    ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A.abelian ρ n τ).hom.app (.op T)).hom.map_one).trans
    ((PELModuli.CMPoints.BlocksProjectors.blockInclusion A.abelian ρ (j.localCharacter iota τ) n).app (.op T)).hom.map_one

omit [IsAlgClosed k] in
theorem prescribedChosenPoint_one
    (H : FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n)) :
    Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n τ H T 1 = 1 :=
  (congrArg (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n τ T)
    (MonObj.one_comp H.inclusion.hom.hom)).trans
    (canonicalOriginalBlockPoint_one A j iota hsplit ρ n τ T)

omit [IsAlgClosed k] in
theorem canonicalOriginalBlockPoint_component_self :
    Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n τ T
      (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n τ T x) =
        CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n τ T x := by
  apply Subtype.ext
  exact PELModuli.CMPoints.BlockDecomposition.block_projector_self j iota hsplit A.abelian ρ n τ T
    ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A.abelian ρ n τ).hom.app (.op T) x)

omit [IsAlgClosed k] in
theorem canonicalOriginalBlockPoint_component_other (σ : Gal(E/ℚ)) (h : τ ≠ σ) :
    Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n σ T
      (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n τ T x) = 1 := by
  apply Subtype.ext
  exact PELModuli.CMPoints.BlockDecomposition.block_projector_other j iota hsplit A.abelian ρ n τ σ h T
    ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A.abelian ρ n τ).hom.app (.op T) x)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalBlockProjectorPoints.Construction
