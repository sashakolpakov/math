import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.ReducedFiberConstants

/-! # Reduced Family Affine Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.ReducedFamilyAffineRigidity

noncomputable section

/-! Affine-valued maps from reduced proper geometrically connected reduced families factor through a section. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X S Y : Scheme.{u}}

theorem connectedReducedFamily_affineMap_eq (p : X ⟶ S) [IsReduced X]
    [UniversallyClosed p] [GeometricallyConnected p] [GeometricallyReduced p] (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 _)
    (f : X ⟶ Y) [IsAffine Y] : f = p ≫ σ ≫ f := by
  apply ext_of_fromSpecResidueField_eq f (p ≫ σ ≫ f) (terminal.from Y) Set.univ dense_univ
  · intro z _
    exact ReducedFiberConstants.properConnectedReducedFamily_affineMap_residue p σ hσ f z
  · exact Subsingleton.elim _ _

theorem connectedReducedFamily_affineFactorization (p : X ⟶ S) [IsReduced X]
    [UniversallyClosed p] [GeometricallyConnected p] [GeometricallyReduced p] (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 _)
    (f : X ⟶ Y) [IsAffine Y] : ∃! a : S ⟶ Y, p ≫ a = f := by
  refine ⟨σ ≫ f, (connectedReducedFamily_affineMap_eq p σ hσ f).symm, ?_⟩
  intro a ha
  exact (Category.id_comp a).symm.trans
    ((congrArg (fun k => k ≫ a) hσ.symm).trans
      ((Category.assoc _ _ _).trans (congrArg (fun k => σ ≫ k) ha)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.ReducedFamilyAffineRigidity
