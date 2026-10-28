import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.PairingValues
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CMPointsBlockComparison

/-! # Block Pairing -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.BlockPairing

noncomputable section

/-! The actual canonical source pairing on the original CMPoints blocks.
The comparison fixes their embeddings and all scheme-valued points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.PairingValues

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)

def originalBlockNativeTorsionMap (n : ℕ) (τ : Gal(E/ℚ)) :
    (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n).X ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.abelian.scheme (q ^ n) :=
  (Intrinsic.CMPointsBlockComparison.nativeCMPointsBlockGroupIso j iota hsplit A.abelian ρ n τ).inv.hom.hom ≫
    AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointInclusion (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap (q ^ n) (ρ.map (j.projector iota hsplit n τ)))

instance originalBlockNativeTorsionMap_isMonHom (n : ℕ) (τ : Gal(E/ℚ)) :
    IsMonHom (originalBlockNativeTorsionMap j iota hsplit A ρ n τ) := by
  unfold originalBlockNativeTorsionMap
  infer_instance

omit [IsAlgClosed k] in
theorem originalBlockNativeTorsionMap_inclusion (n : ℕ) (τ : Gal(E/ℚ)) :
    originalBlockNativeTorsionMap j iota hsplit A ρ n τ ≫
      AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.abelian.scheme (q ^ n) =
        AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n τ := by
  let e : AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (ρ.map (j.projector iota hsplit n τ)) ≅
      (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n).X :=
    (Grp.forget _).mapIso
      (Intrinsic.CMPointsBlockComparison.nativeCMPointsBlockGroupIso j iota hsplit A.abelian ρ n τ)
  change (e.inv ≫ AbelianScheme.IsogenyQuotient.BlockGroups.Construction.fixedPointInclusion _) ≫ _ = _
  rw [Category.assoc]
  change e.inv ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n τ)) = _
  have he : e.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n τ =
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n τ)) :=
    Intrinsic.CMPointsBlockComparison.nativeCMPointsBlockGroupIso_inclusion j iota hsplit A.abelian ρ n τ
  rw [← he, e.inv_hom_id_assoc]

omit [IsAlgClosed k] in
theorem originalBlockNativeTorsionMap_point (n : ℕ) (τ : Gal(E/ℚ))
    (T : Over (Spec (.of k))) (b : T ⟶ (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n).X) :
    AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift A.abelian.scheme (q ^ n)
      ((PELModuli.CMPoints.BlocksProjectors.blockInclusion A.abelian ρ (j.localCharacter iota τ) n).app (.op T)
        ((AbelianScheme.FrobeniusKernel.CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A.abelian ρ n τ).hom.app (.op T) b)).val
      ((PELModuli.CMPoints.BlocksProjectors.blockInclusion A.abelian ρ (j.localCharacter iota τ) n).app (.op T)
        ((AbelianScheme.FrobeniusKernel.CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A.abelian ρ n τ).hom.app (.op T) b)).property =
      b ≫ originalBlockNativeTorsionMap j iota hsplit A ρ n τ := by
  apply (cancel_mono (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.abelian.scheme (q ^ n))).mp
  change AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift A.abelian.scheme (q ^ n)
      (b ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n τ) _ ≫ _ = _
  refine (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift_inclusion A.abelian.scheme (q ^ n)
    (b ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n τ) _).trans ?_
  exact ((Category.assoc b (originalBlockNativeTorsionMap j iota hsplit A ρ n τ)
    (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.abelian.scheme (q ^ n))).trans
      (congrArg (fun z => b ≫ z)
        (originalBlockNativeTorsionMap_inclusion j iota hsplit A ρ n τ))).symm

def prescribedOriginalBlockPairing (n : ℕ) (τ υ : Gal(E/ℚ)) :
    AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n).X)
      (B := (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ υ n).X)
      (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X) :=
  (PairingValues.prescribedNativePairing A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n)).restrict
    (originalBlockNativeTorsionMap j iota hsplit A ρ n τ)
    (originalBlockNativeTorsionMap j iota hsplit A ρ n υ)

theorem canonicalTorsionOrthogonal_original_blocks (n : ℕ) (τ υ : Gal(E/ℚ))
    (T : Over (Spec (.of k)))
    (a : T ⟶ (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n).X)
    (b : T ⟶ (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ υ n).X) :
    AbelianScheme.FrobeniusKernel.Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) T
      ((PELModuli.CMPoints.BlocksProjectors.blockInclusion A.abelian ρ (j.localCharacter iota τ) n).app (.op T)
        ((AbelianScheme.FrobeniusKernel.CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A.abelian ρ n τ).hom.app (.op T) a))
      ((PELModuli.CMPoints.BlocksProjectors.blockInclusion A.abelian ρ (j.localCharacter iota υ) n).app (.op T)
        ((AbelianScheme.FrobeniusKernel.CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A.abelian ρ n υ).hom.app (.op T) b)) ↔
      (prescribedOriginalBlockPairing j iota hsplit A ρ n τ υ).pairValue a b = 1 := by
  rw [PairingValues.canonicalTorsionOrthogonal_native, originalBlockNativeTorsionMap_point,
    originalBlockNativeTorsionMap_point]
  rw [prescribedOriginalBlockPairing, AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.restrict_pairValue]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.BlockPairing
