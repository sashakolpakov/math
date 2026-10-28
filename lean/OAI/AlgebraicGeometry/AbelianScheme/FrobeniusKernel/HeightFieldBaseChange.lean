import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DivisibleFieldBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BlockFieldBaseChange

/-! # Height Field Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HeightFieldBaseChange.Construction

noncomputable section

/-! Field extension preserves the full CMPoints block-height conclusion.
The new q-divisible tower and its affine block representations are
constructed, and the original transition compatibility is transported. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k k' : Type} [Field k] [Field k'] [Algebra k k']
variable {O : Type} [CommRing O] {g q : ℕ} [Fact q.Prime]
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A)
variable (χ : O →+* PadicInt q) {h : ℕ} (G : GroupSchemes.FiniteEtale.PDivisibleGroup k q h)
variable (e : ∀ n : ℕ, (G.level n).points ⋙ forget₂ CommGrpCat GrpCat ≅
  PELModuli.CMPoints.BlocksProjectors.affineBlockFunctor A ρ χ n)

def l45HeightFieldBaseChangeRepresentation (n : ℕ) :
    ((DivisibleFieldBaseChange.Construction.pDivisibleGroupFieldBaseChange (k' := k') G).level n).points ⋙ forget₂ CommGrpCat GrpCat ≅
      PELModuli.CMPoints.BlocksProjectors.affineBlockFunctor
        (A.pullback (GroupFieldBaseChange.Construction.finiteGroupFieldBaseMap (k := k) (k' := k')))
        (ρ.pullback (GroupFieldBaseChange.Construction.finiteGroupFieldBaseMap (k := k) (k' := k'))) χ n :=
  FieldBaseChangePoints.Construction.finiteGroupFieldBaseChangePointsIso (k' := k') (G.level n) ≪≫
    Functor.isoWhiskerLeft (AffineFieldRestriction.Construction.restrictFieldAlgebras (k := k) (k' := k')) (e n) ≪≫
      (BlockFieldBaseChange.Construction.l45AffineBlockFieldBaseChangeIso (k' := k') A ρ χ n).symm

theorem l45HeightFieldBaseChangeRepresentation_comparison (n : ℕ) (R : CommAlgCat k')
    (x : GroupSchemes.FiniteEtale.affine k' R ⟶ ((DivisibleFieldBaseChange.Construction.pDivisibleGroupFieldBaseChange (k' := k') G).level n).scheme) :
    (BlockFieldBaseChange.Construction.l45AffineBlockFieldBaseChangeIso (k' := k') A ρ χ n).hom.app R
        ((l45HeightFieldBaseChangeRepresentation (k' := k') A ρ χ G e n).hom.app R x) =
      (e n).hom.app (AffineFieldRestriction.Construction.restrictFieldAlgebra (k := k) R)
        ((FieldBaseChangePoints.Construction.finiteGroupFieldBaseChangePointsIso (k' := k') (G.level n)).hom.app R x) := by
  let α := BlockFieldBaseChange.Construction.l45AffineBlockFieldBaseChangeIso (k' := k') A ρ χ n
  let y := (e n).hom.app (AffineFieldRestriction.Construction.restrictFieldAlgebra (k := k) R)
    ((FieldBaseChangePoints.Construction.finiteGroupFieldBaseChangePointsIso (k' := k') (G.level n)).hom.app R x)
  change α.hom.app R (α.inv.app R y) = y
  exact ConcreteCategory.congr_hom (NatTrans.congr_app α.inv_hom_id R) y

variable (ht : ∀ (n : ℕ) (R : CommAlgCat k) (x : GroupSchemes.FiniteEtale.affine k R ⟶ (G.level n).scheme),
  (((e (n + 1)).hom.app R) (x ≫ G.inclusion n)).val = (((e n).hom.app R) x).val)

include ht in
theorem l45HeightFieldBaseChangeRepresentation_transition (n : ℕ) (R : CommAlgCat k')
    (x : GroupSchemes.FiniteEtale.affine k' R ⟶ ((DivisibleFieldBaseChange.Construction.pDivisibleGroupFieldBaseChange (k' := k') G).level n).scheme) :
    (((l45HeightFieldBaseChangeRepresentation (k' := k') A ρ χ G e (n + 1)).hom.app R)
        (x ≫ (DivisibleFieldBaseChange.Construction.pDivisibleGroupFieldBaseChange (k' := k') G).inclusion n)).val =
      (((l45HeightFieldBaseChangeRepresentation (k' := k') A ρ χ G e n).hom.app R) x).val := by
  let z₁ := ((l45HeightFieldBaseChangeRepresentation (k' := k') A ρ χ G e (n + 1)).hom.app R)
    (x ≫ (DivisibleFieldBaseChange.Construction.pDivisibleGroupFieldBaseChange (k' := k') G).inclusion n)
  let z₀ := ((l45HeightFieldBaseChangeRepresentation (k' := k') A ρ χ G e n).hom.app R) x
  apply (A.baseChangePointsMulEquiv (GroupFieldBaseChange.Construction.finiteGroupFieldBaseMap (k := k) (k' := k'))
    (GroupSchemes.FiniteEtale.affine k' R)).injective
  apply (cancel_epi (AffineFieldRestriction.Construction.restrictedAffineBaseIso (k := k) R).inv).mp
  have h₁ := BlockFieldBaseChange.Construction.l45AffineBlockFieldBaseChangeIso_value (k' := k') A ρ χ (n + 1) R z₁
  have h₂ := congrArg Subtype.val
    (l45HeightFieldBaseChangeRepresentation_comparison (k' := k') A ρ χ G e (n + 1) R
      (x ≫ (DivisibleFieldBaseChange.Construction.pDivisibleGroupFieldBaseChange (k' := k') G).inclusion n))
  have h₃ := congrArg (fun y => ((e (n + 1)).hom.app (AffineFieldRestriction.Construction.restrictFieldAlgebra (k := k) R) y).val)
    (FieldBaseChangePoints.Construction.finiteGroupFieldBaseChangePointsIso_postcomp (k' := k') (G.inclusion n) R x)
  have h₄ := ht n (AffineFieldRestriction.Construction.restrictFieldAlgebra (k := k) R)
    ((FieldBaseChangePoints.Construction.finiteGroupFieldBaseChangePointsIso (k' := k') (G.level n)).hom.app R x)
  have h₅ := congrArg Subtype.val
    (l45HeightFieldBaseChangeRepresentation_comparison (k' := k') A ρ χ G e n R x)
  have h₆ := BlockFieldBaseChange.Construction.l45AffineBlockFieldBaseChangeIso_value (k' := k') A ρ χ n R z₀
  exact h₁.symm.trans (h₂.trans (h₃.trans (h₄.trans (h₅.symm.trans h₆))))

theorem l45BlockHasHeight_fieldBaseChange (hA : PELModuli.CMPoints.BlocksProjectors.BlockHasHeight A ρ χ h) :
    PELModuli.CMPoints.BlocksProjectors.BlockHasHeight
      (A.pullback (GroupFieldBaseChange.Construction.finiteGroupFieldBaseMap (k := k) (k' := k')))
      (ρ.pullback (GroupFieldBaseChange.Construction.finiteGroupFieldBaseMap (k := k) (k' := k'))) χ h := by
  obtain ⟨G, e, ht⟩ := hA
  exact ⟨DivisibleFieldBaseChange.Construction.pDivisibleGroupFieldBaseChange (k' := k') G,
    l45HeightFieldBaseChangeRepresentation (k' := k') A ρ χ G e,
    l45HeightFieldBaseChangeRepresentation_transition (k' := k') A ρ χ G e ht⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HeightFieldBaseChange.Construction
