import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FactoredBaseRecovery

/-! # Intersection Recovery Base Factor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The original chart recovery maps factor through the chosen finite coefficient extension. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Over (Spec (.of R))}
variable [CompactSpace X.left] [IsSeparated X.hom] (M : FiniteIntersection.IntersectionModel.FiniteIntersectionModel X)
variable (D : Subalgebra M.coefficients R)

theorem FiniteIntersection.IntersectionModel.FiniteIntersectionModel.coefficientBaseFactor :
    Spec.map (CommRingCat.ofHom D.val.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap M.coefficients D)) =
      Spec.map (CommRingCat.ofHom M.coefficients.val.toRingHom) := by
  rw [← Spec.map_comp]
  rfl

theorem FiniteIntersection.IntersectionModel.FiniteIntersectionModel.chartRecovery_factored_isPullback (S : Finite.AffineIntersections.finiteIntersectionIndex X) :
    IsPullback (FiniteIntersection.IntersectionModel.finiteIntersectionModelMap X M S) (Finite.AffineIntersections.finiteIntersectionChart X S).hom (M.chartMap S)
      (Spec.map (CommRingCat.ofHom D.val.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap M.coefficients D))) := by
  rw [M.coefficientBaseFactor]
  exact FiniteIntersection.IntersectionModel.finiteIntersectionModelMap_isPullback X M S

def FiniteIntersection.IntersectionModel.FiniteIntersectionModel.chartBaseChangeRecovery (S : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ) :
    (Finite.AffineIntersections.finiteIntersectionChart X S).left ⟶ ((M.baseChangedFunctor D).obj S).left :=
  FactoredBaseRecovery.factoredBaseRecovery _ _ _ _ _ (M.chartRecovery_factored_isPullback D S)

theorem FiniteIntersection.IntersectionModel.FiniteIntersectionModel.chartBaseChangeRecovery_fst (S : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ) :
    M.chartBaseChangeRecovery D S ≫ pullback.fst (M.chartMap S)
      (Spec.map (CommRingCat.ofHom (algebraMap M.coefficients D))) = FiniteIntersection.IntersectionModel.finiteIntersectionModelMap X M S :=
  FactoredBaseRecovery.factoredBaseRecovery_fst _ _ _ _ _ _

theorem FiniteIntersection.IntersectionModel.FiniteIntersectionModel.chartBaseChangeRecovery_snd (S : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ) :
    M.chartBaseChangeRecovery D S ≫ ((M.baseChangedFunctor D).obj S).hom =
      (Finite.AffineIntersections.finiteIntersectionChart X S).hom ≫ Spec.map (CommRingCat.ofHom D.val.toRingHom) :=
  FactoredBaseRecovery.factoredBaseRecovery_snd _ _ _ _ _ _

theorem FiniteIntersection.IntersectionModel.FiniteIntersectionModel.chartBaseChangeRecovery_isPullback (S : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ) :
    IsPullback (M.chartBaseChangeRecovery D S) (Finite.AffineIntersections.finiteIntersectionChart X S).hom
      ((M.baseChangedFunctor D).obj S).hom (Spec.map (CommRingCat.ofHom D.val.toRingHom)) :=
  FactoredBaseRecovery.factoredBaseRecovery_isPullback _ _ _ _ _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
