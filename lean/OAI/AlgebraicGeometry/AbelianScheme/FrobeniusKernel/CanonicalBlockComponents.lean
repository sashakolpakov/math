import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalSheafBlockPairing
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.RepresentedIntrinsicIso
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SheafPairingValues
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierIntrinsicRepresentation
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsSplittingPoints

/-! # Canonical Block Components -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalBlockComponents.Construction

noncomputable section

section

/-! The canonical block pairing determines the actual native opposite
Cartier isomorphism, retaining the original kernel-prescription values. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
variable (n : ℕ) (τ : Gal(E/ℚ))

local instance canonicalChosenBlock_comm (υ : Gal(E/ℚ)) :
    IsCommMonObj (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ υ n).X :=
  (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A.abelian ρ n υ).comm

def canonicalOriginalBlockPoint (T : Over (Spec (.of k)))
    (x : T ⟶ (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n).X) :
    (A.abelian.torsionFunctor (q ^ n)).obj (.op T) :=
  (PELModuli.CMPoints.BlocksProjectors.blockInclusion A.abelian ρ (j.localCharacter iota τ) n).app (.op T)
    ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A.abelian ρ n τ).hom.app (.op T) x)

variable (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (hgood : q.Coprime (∏ i, δ i))
variable (C : CartierModel.Construction.CartierCoordinates (.of k) (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n))

local instance : IsCommMonObj C.dualGroup.X := C.dualGroup_commutative

def canonicalSheafCartierGroupIso :
    CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ) n ≅ C.dualGroup := by
  let b := CanonicalSheafBlockPairing.Construction.canonicalSheafBlockPairing j iota hsplit A ρ n τ
  have h := CanonicalSheafBlockPairing.Construction.canonicalSheafBlockPairing_isPerfect j iota hsplit A ρ n τ hρ hgood
  let e := @asIso _ _ _ _ b.rightAdjoint h.2
  exact RepresentedIntrinsicIso.Construction.representedNativeGroupIso _ _ (e ≪≫ C.representedCartierDualIso.symm)

theorem canonicalSheafCartierGroupIso_character :
    CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (canonicalSheafCartierGroupIso j iota hsplit A ρ n τ hρ hgood C).hom ≫
      C.representedCartierDualIso.hom = (CanonicalSheafBlockPairing.Construction.canonicalSheafBlockPairing j iota hsplit A ρ n τ).rightAdjoint := by
  let b := CanonicalSheafBlockPairing.Construction.canonicalSheafBlockPairing j iota hsplit A ρ n τ
  have hb := CanonicalSheafBlockPairing.Construction.canonicalSheafBlockPairing_isPerfect j iota hsplit A ρ n τ hρ hgood
  let e := @asIso _ _ _ _ b.rightAdjoint hb.2
  have h := RepresentedIntrinsicIso.Construction.representedNativeGroupIso_hom _ _ (e ≪≫ C.representedCartierDualIso.symm)
  exact (congrArg (fun f => f ≫ C.representedCartierDualIso.hom) h).trans
    ((Category.assoc e.hom C.representedCartierDualIso.inv C.representedCartierDualIso.hom).trans
      ((congrArg (fun f => e.hom ≫ f) C.representedCartierDualIso.inv_hom_id).trans
        (Category.comp_id e.hom)))

omit hρ hgood C in
theorem canonicalSheafBlockPairing_value (T : Over (Spec (.of k)))
    (x : T ⟶ (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n).X)
    (y : T ⟶ (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ) n).X) :
    CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CanonicalSheafBlockRetraction.Construction.canonicalBlockSheaf j iota hsplit A.abelian ρ n τ) T
      ((CanonicalSheafBlockPairing.Construction.canonicalSheafBlockPairing j iota hsplit A ρ n τ).rightAdjoint.hom.app (.op T) (ULift.up y)) (ULift.up x) =
      CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian) (q ^ n)) T
        ((CartierDualityCanonical.Construction.e56SourceTorsionPairing A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n)).rightAdjoint.hom.app (.op T)
          (Prescription.Construction.originalTorsionSheafPoint A.abelian (q ^ n) T
            ((PELModuli.CMPoints.BlocksProjectors.blockInclusion A.abelian ρ (j.localCharacter iota (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ)) n).app (.op T)
              ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A.abelian ρ n (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ)).hom.app (.op T) y))))
        (Prescription.Construction.originalTorsionSheafPoint A.abelian (q ^ n) T
          ((PELModuli.CMPoints.BlocksProjectors.blockInclusion A.abelian ρ (j.localCharacter iota τ) n).app (.op T)
            ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A.abelian ρ n τ).hom.app (.op T) x))) := by
  let e := CartierDualityCanonical.Construction.e56SourceTorsionPairing A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n)
  exact (SheafPairingValues.Construction.sheafPairing_restrict_value e
    (CanonicalSheafBlockRetraction.Construction.canonicalBlockSheafInclusion j iota hsplit A.abelian ρ n τ)
    (CanonicalSheafBlockRetraction.Construction.canonicalBlockSheafInclusion j iota hsplit A.abelian ρ n (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ)) T
    (ULift.up x) (ULift.up y)).trans
      (congrArg₂ (fun x y => CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue
        (CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian) (q ^ n)) T
        (e.rightAdjoint.hom.app (.op T) y) x)
        (CanonicalSheafBlockPoints.Construction.canonicalBlockSheafInclusion_value j iota hsplit A.abelian ρ n τ T x)
        (CanonicalSheafBlockPoints.Construction.canonicalBlockSheafInclusion_value j iota hsplit A.abelian ρ n (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ) T y))

theorem canonicalSheafCartierGroupIso_orthogonal (T : Over (Spec (.of k)))
    (x : T ⟶ (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n).X)
    (y : T ⟶ (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ) n).X) :
    ((C.pointsEquiv T (y ≫ (canonicalSheafCartierGroupIso j iota hsplit A ρ n τ hρ hgood C).hom.hom.hom)).app
      (.op (Over.mk (𝟙 T)))) x = 1 ↔
    Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) T
      (canonicalOriginalBlockPoint j iota hsplit A ρ n τ T x)
      (canonicalOriginalBlockPoint j iota hsplit A ρ n (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ) T y) := by
  have he := congrArg (fun f => f.hom.app (.op T) (ULift.up y))
    (canonicalSheafCartierGroupIso_character j iota hsplit A ρ n τ hρ hgood C)
  have hc := C.representedCartierDualIso_value T
    (y ≫ (canonicalSheafCartierGroupIso j iota hsplit A ρ n τ hρ hgood C).hom.hom.hom) x
  have hval := hc.symm.trans ((congrArg (fun z =>
    CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CanonicalSheafBlockRetraction.Construction.canonicalBlockSheaf j iota hsplit A.abelian ρ n τ) T z (ULift.up x)) he).trans
      (canonicalSheafBlockPairing_value j iota hsplit A ρ n τ T x y))
  constructor
  · intro h
    exact hval.symm.trans (congrArg ULift.up h)
  · intro h
    apply ULift.up_injective
    exact hval.trans h

end

/-! Native block coordinates are the exact original projector components,
including under every test-scheme restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
variable (n : ℕ) (τ : Gal(E/ℚ))

theorem canonicalOriginalBlockPoint_injective (T : Over (Spec (.of k))) :
    Function.Injective (canonicalOriginalBlockPoint j iota hsplit A ρ n τ T) := by
  intro x y h
  apply ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A.abelian ρ n τ).app (.op T)).groupIsoToMulEquiv.injective
  apply Subtype.ext
  exact congrArg (fun z : A.abelian.torsionPoints (q ^ n) T => z.val) h

theorem canonicalOriginalBlockPoint_natural {T U : Over (Spec (.of k))} (t : U ⟶ T)
    (y : T ⟶ (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n).X) :
    (A.abelian.torsionFunctor (q ^ n)).map t.op (canonicalOriginalBlockPoint j iota hsplit A ρ n τ T y) =
      canonicalOriginalBlockPoint j iota hsplit A ρ n τ U (t ≫ y) := by
  apply Subtype.ext
  exact (Category.assoc t y
    (PELModuli.CMPoints.BlocksProjectors.idempotentBlockInclusion A.abelian ρ (q ^ n) (j.projector iota hsplit n τ))).symm

theorem prescribedBlockComponent_natural {T U : Over (Spec (.of k))} (t : U ⟶ T)
    (x : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) :
    (A.abelian.torsionFunctor (q ^ n)).map t.op (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n τ T x) =
      Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n τ U ((A.abelian.torsionFunctor (q ^ n)).map t.op x) := by
  apply Subtype.ext
  exact (Category.assoc t x.val (ρ.map (j.projector iota hsplit n τ))).symm

variable (s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))

omit τ in
theorem canonicalFullBlockComponent_false (T : Over (Spec (.of k)))
    (b : T ⟶ (BlockProducts.Construction.groupBlockProduct s (CMPointsSplitting.Construction.l45PairedBlockFamily j iota hsplit A.abelian ρ n s labels)).X)
    (v : Fin s) :
    canonicalOriginalBlockPoint j iota hsplit A ρ n (labels (v, false)) T
      (ProductPoints.Construction.groupBlockProductPointsEquiv s (CMPointsSplitting.Construction.l45PairedBlockFamily j iota hsplit A.abelian ρ n s labels) T b v ≫ fst _ _) =
      Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (labels (v, false)) T
        (CMPointsSplitting.Construction.l45FullBlockPointsEquiv j iota hsplit A.abelian ρ n s labels T b) := by
  have h₁ := CMPointsSplitting.Construction.l45FullBlockCharacters_false j iota hsplit A.abelian ρ n s labels T b v
  have h₂ := congrFun (CMPointsSplitting.Construction.l45FullBlockPointsEquiv_blocks j iota hsplit A.abelian ρ n s labels T b)
    (labels (v, false))
  exact congrArg (fun z => (PELModuli.CMPoints.BlocksProjectors.blockInclusion A.abelian ρ
    (j.localCharacter iota (labels (v, false))) n).app (.op T) z) (h₁.symm.trans h₂.symm)

omit τ in
theorem canonicalFullBlockComponent_true (T : Over (Spec (.of k)))
    (b : T ⟶ (BlockProducts.Construction.groupBlockProduct s (CMPointsSplitting.Construction.l45PairedBlockFamily j iota hsplit A.abelian ρ n s labels)).X)
    (v : Fin s) :
    canonicalOriginalBlockPoint j iota hsplit A ρ n (labels (v, true)) T
      (ProductPoints.Construction.groupBlockProductPointsEquiv s (CMPointsSplitting.Construction.l45PairedBlockFamily j iota hsplit A.abelian ρ n s labels) T b v ≫ snd _ _) =
      Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (labels (v, true)) T
        (CMPointsSplitting.Construction.l45FullBlockPointsEquiv j iota hsplit A.abelian ρ n s labels T b) := by
  have h₁ := CMPointsSplitting.Construction.l45FullBlockCharacters_true j iota hsplit A.abelian ρ n s labels T b v
  have h₂ := congrFun (CMPointsSplitting.Construction.l45FullBlockPointsEquiv_blocks j iota hsplit A.abelian ρ n s labels T b)
    (labels (v, true))
  exact congrArg (fun z => (PELModuli.CMPoints.BlocksProjectors.blockInclusion A.abelian ρ
    (j.localCharacter iota (labels (v, true))) n).app (.op T) z) (h₁.symm.trans h₂.symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalBlockComponents.Construction
