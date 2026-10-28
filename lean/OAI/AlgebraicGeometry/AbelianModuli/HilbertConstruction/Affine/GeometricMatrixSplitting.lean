import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmallIndexMatrixSplitting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.FrameOpenCover

/-! # Geometric Matrix Splitting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GeometricMatrixSplitting

noncomputable section

/-! On an affine base, geometric scheme points test every coefficient
map to an algebraically closed field. Thus geometric injectivity gives
an actual splitting over the affine coordinate ring. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R]
variable {ι ν : Type} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

theorem fieldPointGlobalScalarMap_specMap {K : Type u} [Field K] (φ : R →+* K) :
    Geometric.FrameOpenCover.fieldPointGlobalScalarMap (Spec.map (CommRingCat.ofHom φ)) =
      φ.comp (Scheme.ΓSpecIso (.of R)).hom.hom := by
  ext a
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)) a

def affineCoordinateMatrix (F : Matrix ι ν Γ(Spec (.of R), ⊤)) : Matrix ι ν R :=
  F.map (Scheme.ΓSpecIso (.of R)).hom.hom

omit [Fintype ι] [DecidableEq ι] in
theorem affineCoordinateMatrix_geometric_injective (F : Matrix ι ν Γ(Spec (.of R), ⊤))
    (hF : ∀ (K : Type u) [Field K] [IsAlgClosed K] (q : Spec (.of K) ⟶ Spec (.of R)),
      Function.Injective (Matrix.toLin' (F.map (Geometric.FrameOpenCover.fieldPointGlobalScalarMap q))))
    (K : Type u) [Field K] [IsAlgClosed K] (φ : R →+* K) :
    Function.Injective (Matrix.toLin' ((affineCoordinateMatrix F).map φ)) := by
  have h := hF K (Spec.map (CommRingCat.ofHom φ))
  rw [fieldPointGlobalScalarMap_specMap] at h
  exact h

theorem affineCoordinateMatrix_leftInverse (F : Matrix ι ν Γ(Spec (.of R), ⊤))
    (hF : ∀ (K : Type u) [Field K] [IsAlgClosed K] (q : Spec (.of K) ⟶ Spec (.of R)),
      Function.Injective (Matrix.toLin' (F.map (Geometric.FrameOpenCover.fieldPointGlobalScalarMap q)))) :
    ∃ B : Matrix ν ι R, B * affineCoordinateMatrix F = 1 :=
  SmallIndexMatrixSplitting.smallIndexMatrix_leftInverse_of_geometric_injective _ (affineCoordinateMatrix_geometric_injective F hF)

theorem affineCoordinateMatrix_injective_all_baseChanges
    {C : Type u} [CommRing C] (φ : R →+* C) (F : Matrix ι ν Γ(Spec (.of R), ⊤))
    (hF : ∀ (K : Type u) [Field K] [IsAlgClosed K] (q : Spec (.of K) ⟶ Spec (.of R)),
      Function.Injective (Matrix.toLin' (F.map (Geometric.FrameOpenCover.fieldPointGlobalScalarMap q)))) :
    Function.Injective (Matrix.toLin' ((affineCoordinateMatrix F).map φ)) :=
  SmallIndexMatrixSplitting.smallIndexMatrix_injective_all_baseChanges_of_geometric_injective φ _
    (affineCoordinateMatrix_geometric_injective F hF)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GeometricMatrixSplitting
