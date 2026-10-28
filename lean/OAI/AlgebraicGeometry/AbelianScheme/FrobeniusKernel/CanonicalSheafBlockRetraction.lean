import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescriptionActions
import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockRetraction

/-! # Canonical Sheaf Block Retraction -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalSheafBlockRetraction.Construction

noncomputable section

/-! The original coefficient blocks are actual retracts of the canonical
torsion sheaf. The maps retain the specified original point functors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] {g : ℕ}
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
variable (n : ℕ) (τ : Gal(E/ℚ))

local instance canonicalBlock_comm :
    IsCommMonObj (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).toGrp.X :=
  (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).comm

def canonicalBlockToNativeTorsion :
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).toGrp ⟶
      CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup (Grp.mk A.scheme) (q ^ n) :=
  yonedaGrpFullyFaithful.preimage
    ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n τ).hom ≫
      PELModuli.CMPoints.BlocksProjectors.blockInclusion A ρ (j.localCharacter iota τ) n ≫
        (IntrinsicTorsionFunctor.Construction.nativeTorsionYonedaIso A (q ^ n)).inv)

def nativeTorsionToCanonicalBlock :
    CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup (Grp.mk A.scheme) (q ^ n) ⟶
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).toGrp :=
  yonedaGrpFullyFaithful.preimage
    ((IntrinsicTorsionFunctor.Construction.nativeTorsionYonedaIso A (q ^ n)).hom ≫
      PELModuli.CMPoints.BlockRetraction.torsionProjectionNat j iota hsplit A ρ n τ ≫
        (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n τ).inv)

theorem canonicalBlockNativeRetraction :
    canonicalBlockToNativeTorsion j iota hsplit A ρ n τ ≫
      nativeTorsionToCanonicalBlock j iota hsplit A ρ n τ = 𝟙 _ := by
  apply yonedaGrp.map_injective
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
  dsimp only [canonicalBlockToNativeTorsion, nativeTorsionToCanonicalBlock]
  rw [yonedaGrpFullyFaithful.map_preimage, yonedaGrpFullyFaithful.map_preimage]
  exact PELModuli.CMPoints.BlockRetraction.iso_conjugated_retraction (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n τ)
    (IntrinsicTorsionFunctor.Construction.nativeTorsionYonedaIso A (q ^ n)) _ _ (PELModuli.CMPoints.BlockRetraction.blockInclusion_projection j iota hsplit A ρ n τ)

def canonicalBlockSheaf : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb (Spec (.of k)) :=
  CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb _ (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).toGrp

def canonicalBlockSheafInclusion :
    canonicalBlockSheaf j iota hsplit A ρ n τ ⟶
      CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A) (q ^ n) :=
  CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (canonicalBlockToNativeTorsion j iota hsplit A ρ n τ) ≫
    (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk A.scheme) (q ^ n)).hom

def canonicalBlockSheafProjection :
    CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A) (q ^ n) ⟶
      canonicalBlockSheaf j iota hsplit A ρ n τ :=
  (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk A.scheme) (q ^ n)).inv ≫
    CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (nativeTorsionToCanonicalBlock j iota hsplit A ρ n τ)

theorem canonicalBlockSheafRetraction :
    canonicalBlockSheafInclusion j iota hsplit A ρ n τ ≫
      canonicalBlockSheafProjection j iota hsplit A ρ n τ = 𝟙 _ := by
  let a := canonicalBlockToNativeTorsion j iota hsplit A ρ n τ
  let b := nativeTorsionToCanonicalBlock j iota hsplit A ρ n τ
  have h : CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap a ≫ CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap b =
      𝟙 (canonicalBlockSheaf j iota hsplit A ρ n τ) :=
    (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp a b).symm.trans
      ((congrArg (fun f => CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap f)
        (canonicalBlockNativeRetraction j iota hsplit A ρ n τ)).trans
          (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_id _))
  exact (Category.assoc (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap a)
    (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk A.scheme) (q ^ n)).hom
    ((CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk A.scheme) (q ^ n)).inv ≫ CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap b)).trans
      ((congrArg (fun f => CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap a ≫ f)
        ((CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk A.scheme) (q ^ n)).hom_inv_id_assoc
          (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap b))).trans h)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalSheafBlockRetraction.Construction
