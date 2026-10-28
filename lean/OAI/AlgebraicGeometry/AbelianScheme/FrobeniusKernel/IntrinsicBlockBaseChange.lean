import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsBlockRepresentation
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BlockBaseChangePoints
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterBaseChange

/-! # Intrinsic Block Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicBlockBaseChange.Construction

noncomputable section

section

/-! Base change of the actual CMPoints block group schemes, obtained from
the exact character-block comparison and native Yoneda representation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
variable (hsplit : j.HasSplitCoordinates iota)
variable {S S' : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
variable (f : S' ⟶ S) (n : ℕ) (τ : Gal(E/ℚ))

local instance l45BlockPullbackMonoidal : (Over.pullback f).Monoidal :=
  Over.instBraidedPullback.toMonoidal

def l45NativeBlockBaseChangePointIso :
    yonedaGrp.obj ((Over.pullback f).mapGrp.obj
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).toGrp) ≅
    yonedaGrp.obj (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit (A.pullback f) (ρ.pullback f) n τ).toGrp :=
  (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackGroupPointIso f
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).toGrp).symm ≪≫
    Functor.isoWhiskerLeft (Over.map f).op (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n τ) ≪≫
      (BlockBaseChangePoints.Construction.l45BlockFunctorBaseChangeIso A ρ f (j.localCharacter iota τ) n).symm ≪≫
        (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit (A.pullback f) (ρ.pullback f) n τ).symm

def l45NativeBlockBaseChangeIso :
    (Over.pullback f).mapGrp.obj (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).toGrp ≅
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit (A.pullback f) (ρ.pullback f) n τ).toGrp :=
  (yonedaGrpFullyFaithful (C := Over S')).preimageIso
    (l45NativeBlockBaseChangePointIso j iota hsplit A ρ f n τ)

theorem l45NativeBlockBaseChangeIso_points (T : Over S')
    (x : T ⟶ (Over.pullback f).obj (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X) :
    x ≫ (l45NativeBlockBaseChangeIso j iota hsplit A ρ f n τ).hom.hom.hom =
      (l45NativeBlockBaseChangePointIso j iota hsplit A ρ f n τ).hom.app (op T) x := by
  have h := (yonedaGrpFullyFaithful (C := Over S')).map_preimage
    (l45NativeBlockBaseChangePointIso j iota hsplit A ρ f n τ).hom
  exact congrArg (fun a => (a.app (op T)).hom x) h

end

/-! The native block base-change isomorphism retains its exact
inclusion into the original abelian scheme, on every test object. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
variable (hsplit : j.HasSplitCoordinates iota)
variable {S S' : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
variable (f : S' ⟶ S) (n : ℕ) (τ : Gal(E/ℚ))

theorem l45NativeBlockBaseChangeIso_blockPoints (T : Over S')
    (x : T ⟶ (Over.pullback f).obj (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X) :
    BlockBaseChangePoints.Construction.l45BlockBaseChangePointsEquiv A ρ f (j.localCharacter iota τ) n T
      ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit (A.pullback f) (ρ.pullback f) n τ).hom.app (op T)
        (x ≫ (l45NativeBlockBaseChangeIso j iota hsplit A ρ f n τ).hom.hom.hom)) =
      (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n τ).hom.app (op ((Over.map f).obj T))
        (((Over.mapPullbackAdj f).homEquiv T
          (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X).symm x) := by
  have h := (yonedaGrpFullyFaithful (C := Over S')).map_preimage
    (l45NativeBlockBaseChangePointIso j iota hsplit A ρ f n τ).hom
  have hc := congrArg (fun a => a ≫
    (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit (A.pullback f) (ρ.pullback f) n τ).hom ≫
      (BlockBaseChangePoints.Construction.l45BlockFunctorBaseChangeIso A ρ f (j.localCharacter iota τ) n).hom) h
  simp only [l45NativeBlockBaseChangePointIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] at hc
  exact congrArg (fun a => (a.app (op T)).hom x) hc

theorem l45NativeBlockBaseChangeIso_inclusion :
    (l45NativeBlockBaseChangeIso j iota hsplit A ρ f n τ).hom.hom.hom ≫
        PELModuli.CMPoints.BlocksProjectors.idempotentBlockInclusion (A.pullback f) (ρ.pullback f) (q ^ n) (j.projector iota hsplit n τ) =
      (Over.pullback f).map
        (PELModuli.CMPoints.BlocksProjectors.idempotentBlockInclusion A ρ (q ^ n) (j.projector iota hsplit n τ)) := by
  let V := (Over.pullback f).obj (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X
  apply (A.baseChangePointsMulEquiv f V).injective
  have h := congrArg Subtype.val
    (l45NativeBlockBaseChangeIso_blockPoints j iota hsplit A ρ f n τ V (𝟙 V))
  refine h.trans ?_
  apply Over.OverMorphism.ext
  change ((𝟙 V.left) ≫ CategoryTheory.Limits.pullback.fst
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom f) ≫
        (PELModuli.CMPoints.BlocksProjectors.idempotentBlockInclusion A ρ (q ^ n) (j.projector iota hsplit n τ)).left =
    ((Over.pullback f).map
      (PELModuli.CMPoints.BlocksProjectors.idempotentBlockInclusion A ρ (q ^ n) (j.projector iota hsplit n τ))).left ≫
        CategoryTheory.Limits.pullback.fst A.scheme.hom f
  rw [Category.id_comp]
  exact (CategoryTheory.Limits.pullback.lift_fst _ _ _).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicBlockBaseChange.Construction
