import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntersectionRecoveryBaseFactor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReferenceIntersectionFunctor

/-! # Intersection Recovery Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Factored chart recovery commutes with all arrows of the base-changed intersection diagram. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Over (Spec (.of R))}
variable [CompactSpace X.left] [IsSeparated X.hom] (M : FiniteIntersection.IntersectionModel.FiniteIntersectionModel X)
variable (D : Subalgebra M.coefficients R)

theorem FiniteIntersection.IntersectionModel.FiniteIntersectionModel.baseChangedMap_fst {S T : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ} (h : S ⟶ T) :
    ((M.baseChangedFunctor D).map h).left ≫ pullback.fst (M.chartMap T)
      (Spec.map (CommRingCat.ofHom (algebraMap M.coefficients D))) =
      pullback.fst (M.chartMap S) (Spec.map (CommRingCat.ofHom (algebraMap M.coefficients D))) ≫
        M.inclusion (leOfHom h) := by
  change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
  exact pullback.lift_fst _ _ _

theorem FiniteIntersection.IntersectionModel.FiniteIntersectionModel.chartBaseChangeRecovery_natural {S T : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ} (h : S ⟶ T) :
    ((ReferenceIntersectionFunctor.originalIntersectionFunctor X).map h).left ≫ M.chartBaseChangeRecovery D T =
      M.chartBaseChangeRecovery D S ≫ ((M.baseChangedFunctor D).map h).left := by
  let c := Spec.map (CommRingCat.ofHom (algebraMap M.coefficients D))
  let f₀ : (Finite.AffineIntersections.finiteIntersectionChart X S).left ⟶ (Finite.AffineIntersections.finiteIntersectionChart X T).left :=
    (FiniteIntersection.Arrows.finiteIntersectionArrow X (leOfHom h)).left
  let fD : pullback (M.chartMap S) c ⟶ pullback (M.chartMap T) c :=
    ((M.baseChangedFunctor D).map h).left
  let qS : (Finite.AffineIntersections.finiteIntersectionChart X S).left ⟶ pullback (M.chartMap S) c :=
    M.chartBaseChangeRecovery D S
  let qT : (Finite.AffineIntersections.finiteIntersectionChart X T).left ⟶ pullback (M.chartMap T) c :=
    M.chartBaseChangeRecovery D T
  have hS₁ : qS ≫ pullback.fst (M.chartMap S) c = FiniteIntersection.IntersectionModel.finiteIntersectionModelMap X M S :=
    M.chartBaseChangeRecovery_fst D S
  have hT₁ : qT ≫ pullback.fst (M.chartMap T) c = FiniteIntersection.IntersectionModel.finiteIntersectionModelMap X M T :=
    M.chartBaseChangeRecovery_fst D T
  have hf₁ : fD ≫ pullback.fst (M.chartMap T) c =
      pullback.fst (M.chartMap S) c ≫ M.inclusion (leOfHom h) := M.baseChangedMap_fst D h
  have hS₂ : qS ≫ pullback.snd (M.chartMap S) c =
      (Finite.AffineIntersections.finiteIntersectionChart X S).hom ≫ Spec.map (CommRingCat.ofHom D.val.toRingHom) :=
    M.chartBaseChangeRecovery_snd D S
  have hT₂ : qT ≫ pullback.snd (M.chartMap T) c =
      (Finite.AffineIntersections.finiteIntersectionChart X T).hom ≫ Spec.map (CommRingCat.ofHom D.val.toRingHom) :=
    M.chartBaseChangeRecovery_snd D T
  have hf₂ : fD ≫ pullback.snd (M.chartMap T) c = pullback.snd (M.chartMap S) c :=
    ((M.baseChangedFunctor D).map h).w
  change f₀ ≫ qT = qS ≫ fD
  apply pullback.hom_ext
  · rw [Category.assoc, hT₁, Category.assoc, hf₁, ← Category.assoc, hS₁]
    exact (M.inclusion_recovery (leOfHom h)).symm
  · rw [Category.assoc, hT₂, Category.assoc, hf₂, hS₂, ← Category.assoc]
    exact congrArg (fun f => f ≫ Spec.map (CommRingCat.ofHom D.val.toRingHom))
      ((ReferenceIntersectionFunctor.originalIntersectionFunctor X).map h).w

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
