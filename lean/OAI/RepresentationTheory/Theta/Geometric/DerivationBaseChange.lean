import Mathlib.RingTheory.TensorProduct.Finite
import OAI.RepresentationTheory.Theta.Geometric.PointCotangent
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom

/-! # Derivation Base Change -/

namespace OAI.RepresentationTheory.Theta.Geometric.DerivationBaseChange

noncomputable section

section

/-! Extending the residue field extends the actual point-derivation space
by tensor product, with the expected formula on every regular function. -/

open scoped TensorProduct

variable (k A F : Type) [Field k] [CommRing A] [Field F]
  [Algebra k A] [Algebra A k] [IsScalarTower k A k]
  [Algebra k F] [Algebra A F] [IsScalarTower k A F] [IsScalarTower A k F]

def coefficientPointDerivationEquiv :
    Derivation k A F ≃ₗ[F] (PointCotangent.pointCotangent k A →ₗ[k] F) where
  toEquiv := (PointCotangent.pointDerivationEquiv k A F).toEquiv
  map_add' := (PointCotangent.pointDerivationEquiv k A F).map_add
  map_smul' c δ := by
    apply PointCotangent.pointCotangent_linearMap_ext k A
    intro a
    change PointCotangent.pointDerivationEquiv k A F (c • δ) (1 ⊗ₜ[A] KaehlerDifferential.D k A a) =
      c • PointCotangent.pointDerivationEquiv k A F δ (1 ⊗ₜ[A] KaehlerDifferential.D k A a)
    rw [PointCotangent.pointDerivationEquiv_D]
    change c • δ a = c • PointCotangent.pointDerivationEquiv k A F δ (1 ⊗ₜ[A] KaehlerDifferential.D k A a)
    rw [PointCotangent.pointDerivationEquiv_D]

variable [Algebra.EssFiniteType k A]

def pointDerivationBaseChange : F ⊗[k] Derivation k A k ≃ₗ[F] Derivation k A F :=
  ((PointCotangent.pointDerivationEquiv k A k).baseChange k F _ _).trans
    ((IsBaseChange.linearMapRightBaseChangeEquiv (PointCotangent.pointCotangent k A)
      (IsBaseChange.linearMap k F)).trans (coefficientPointDerivationEquiv k A F).symm)

theorem pointDerivationBaseChange_tmul (c : F) (δ : Derivation k A k) (a : A) :
    pointDerivationBaseChange k A F (c ⊗ₜ[k] δ) a = c * algebraMap k F (δ a) := by
  have h := PointCotangent.pointDerivationEquiv_D k A F (pointDerivationBaseChange k A F (c ⊗ₜ[k] δ)) a
  rw [← h]
  change coefficientPointDerivationEquiv k A F
    (pointDerivationBaseChange k A F (c ⊗ₜ[k] δ)) (1 ⊗ₜ[A] KaehlerDifferential.D k A a) = _
  unfold pointDerivationBaseChange
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  change c • algebraMap k F
    (PointCotangent.pointDerivationEquiv k A k δ (1 ⊗ₜ[A] KaehlerDifferential.D k A a)) = _
  rw [PointCotangent.pointDerivationEquiv_D, smul_eq_mul]

end

/-! Residue-field extension commutes with the actual pullback of point
derivations along an algebra morphism. -/

open scoped TensorProduct

variable (k A B F : Type) [Field k] [CommRing A] [CommRing B] [Field F]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
  [Algebra k F] [Algebra A F] [Algebra B F]
  [IsScalarTower k A F] [IsScalarTower k B F] [IsScalarTower A B F]

def pointDerivationComap : Derivation k B F →ₗ[F] Derivation k A F where
  toFun δ := δ.compAlgebraMap A
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [Algebra A k] [Algebra B k]
  [IsScalarTower k A k] [IsScalarTower k B k] [IsScalarTower A B k]
  [IsScalarTower A k F] [IsScalarTower B k F]
  [Algebra.EssFiniteType k A] [Algebra.EssFiniteType k B]

theorem pointDerivationBaseChange_comap (z : F ⊗[k] Derivation k B k) :
    pointDerivationBaseChange k A F ((pointDerivationComap k A B k).baseChange F z) =
      pointDerivationComap k A B F (pointDerivationBaseChange k B F z) := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul c δ =>
      apply Derivation.ext
      intro a
      rw [LinearMap.baseChange_tmul, pointDerivationBaseChange_tmul]
      change c * algebraMap k F (δ (algebraMap A B a)) =
        pointDerivationBaseChange k B F (c ⊗ₜ[k] δ) (algebraMap A B a)
      exact (pointDerivationBaseChange_tmul k B F c δ (algebraMap A B a)).symm

end

end OAI.RepresentationTheory.Theta.Geometric.DerivationBaseChange
