import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Transport

/-! # Lie Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieTransport

noncomputable section

/-! The prescribed Lie ranks are invariant under actual group-scheme
isomorphisms intertwining the integral action. The coordinate maps act
on the original dual-number points and preserve addition and scalars. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k R : Type} [Field k] [CommRing R] {g : ℕ}
  {A B : HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
  (ρ : ActionData.IntegralAction R A) (σ : ActionData.IntegralAction R B)
  (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
  (he : ∀ a : R, ρ.map a ≫ e.hom = e.hom ≫ σ.map a) (τ : R →+* k)

/-- A group isomorphism intertwining the actions transports the actual
Lie eigenpoints, including their infinitesimal base point. -/
def lieEigenpointsEquiv : LieRanks.LieEigenpoints A ρ τ ≃ LieRanks.LieEigenpoints B σ τ where
  toFun x := ⟨x.val ≫ e.hom, by
    constructor
    · exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ e.hom) x.property.1).trans (MonObj.one_comp e.hom))
    · intro a
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun q => x.val ≫ q) (he a).symm).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun q => q ≫ e.hom) (x.property.2 a)).trans (Category.assoc _ _ _))))⟩
  invFun x := ⟨x.val ≫ e.inv, by
    constructor
    · exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ e.inv) x.property.1).trans (MonObj.one_comp e.inv))
    · intro a
      apply (cancel_mono e.hom).mp
      calc
        (x.val ≫ e.inv) ≫ ρ.map a ≫ e.hom = x.val ≫ σ.map a := by
          rw [he a]
          simp only [Category.assoc, Iso.inv_hom_id_assoc]
        _ = LieRanks.dualNumberScalar k (τ a) ≫ x.val := x.property.2 a
        _ = (LieRanks.dualNumberScalar k (τ a) ≫ (x.val ≫ e.inv)) ≫ e.hom := by
          simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]⟩
  left_inv x := Subtype.ext ((Category.assoc _ _ _).trans
    ((congrArg (fun q => x.val ≫ q) e.hom_inv_id).trans (Category.comp_id _)))
  right_inv x := Subtype.ext ((Category.assoc _ _ _).trans
    ((congrArg (fun q => x.val ≫ q) e.inv_hom_id).trans (Category.comp_id _)))

include e he in
/-- Lie rank is preserved with its actual additive and scalar maps. -/
theorem hasLieRank_transport (r : ℕ) (hr : LieRanks.HasLieRank A ρ τ r) : LieRanks.HasLieRank B σ τ r := by
  obtain ⟨c, hadd, hsmul⟩ := hr
  refine ⟨c.trans (lieEigenpointsEquiv ρ σ e he τ), ?_, ?_⟩
  · intro x y
    change (c (x + y)).val ≫ e.hom = ((c x).val ≫ e.hom) * ((c y).val ≫ e.hom)
    exact (congrArg (fun q => q ≫ e.hom) (hadd x y)).trans
      (MonObj.mul_comp (c x).val (c y).val e.hom)
  · intro a x
    change (c (a • x)).val ≫ e.hom = LieRanks.dualNumberScalar k a ≫ ((c x).val ≫ e.hom)
    exact (congrArg (fun q => q ≫ e.hom) (hsmul a x)).trans (Category.assoc _ _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieTransport
