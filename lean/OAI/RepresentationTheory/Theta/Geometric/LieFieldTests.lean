import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TranslationBaseChange

/-! # Lie Field Tests -/

namespace OAI.RepresentationTheory.Theta.Geometric.LieFieldTests

noncomputable section

/-! Lie points on a geometric base change are exactly the original
group's points on the same extended-field dual-number test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable (k F : Type) [Field k] [Field F] [Algebra k F]

def fieldBaseMap : Spec (.of F) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k F))

abbrev extendedDualTest := (Over.map (fieldBaseMap k F)).obj (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest F)

def extendedDualOrigin :
    (Over.map (fieldBaseMap k F)).obj (Over.mk (𝟙 (Spec (.of F)))) ⟶ extendedDualTest k F :=
  (Over.map (fieldBaseMap k F)).map (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin F)

def extendedDualScalar (c : F) : extendedDualTest k F ⟶ extendedDualTest k F :=
  (Over.map (fieldBaseMap k F)).map (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar F c)

variable {R : Type} [CommRing R] {g : ℕ}
  (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) (τ : R →+* F)

def extendedLieEigenpoints :=
  {x : extendedDualTest k F ⟶ A.scheme //
    extendedDualOrigin k F ≫ x = 1 ∧
      ∀ a : R, x ≫ ρ.map a = extendedDualScalar k F (τ a) ≫ x}

def lieFieldTestEquiv :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.LieEigenpoints (A.pullback (fieldBaseMap k F)) (ρ.pullback (fieldBaseMap k F)) τ ≃
      extendedLieEigenpoints k F A ρ τ where
  toFun t := ⟨A.baseChangePointsEquiv (fieldBaseMap k F) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest F) t.val, by
    constructor
    · exact (A.baseChangePointsEquiv_precomp (fieldBaseMap k F)
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin F) t.val).symm.trans
        ((congrArg (A.baseChangePointsEquiv (fieldBaseMap k F) _) t.property.1).trans
          ((A.baseChangePointsMulEquiv (fieldBaseMap k F) _).map_one))
    · intro a
      exact (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map (ρ.map a) (fieldBaseMap k F) _ t.val).symm.trans
        ((congrArg (A.baseChangePointsEquiv (fieldBaseMap k F) _) (t.property.2 a)).trans
          (A.baseChangePointsEquiv_precomp (fieldBaseMap k F) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar F (τ a)) t.val))⟩
  invFun t := ⟨(A.baseChangePointsEquiv (fieldBaseMap k F) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest F)).symm t.val, by
    constructor
    · apply (A.baseChangePointsEquiv (fieldBaseMap k F) _).injective
      rw [A.baseChangePointsEquiv_precomp, Equiv.apply_symm_apply]
      exact t.property.1.trans ((A.baseChangePointsMulEquiv (fieldBaseMap k F) _).map_one).symm
    · intro a
      apply (A.baseChangePointsEquiv (fieldBaseMap k F) _).injective
      change A.baseChangePointsEquiv (fieldBaseMap k F) _
        ((A.baseChangePointsEquiv (fieldBaseMap k F) _).symm t.val ≫
          (Over.pullback (fieldBaseMap k F)).map (ρ.map a)) = _
      rw [AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map, A.baseChangePointsEquiv_precomp,
        Equiv.apply_symm_apply]
      exact t.property.2 a⟩
  left_inv t := Subtype.ext ((A.baseChangePointsEquiv (fieldBaseMap k F) _).symm_apply_apply t.val)
  right_inv t := Subtype.ext ((A.baseChangePointsEquiv (fieldBaseMap k F) _).apply_symm_apply t.val)

theorem lieFieldTestEquiv_mul (t u : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.LieEigenpoints
    (A.pullback (fieldBaseMap k F)) (ρ.pullback (fieldBaseMap k F)) τ)
    (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.LieEigenpoints (A.pullback (fieldBaseMap k F)) (ρ.pullback (fieldBaseMap k F)) τ)
    (hv : v.val = t.val * u.val) :
    (lieFieldTestEquiv k F A ρ τ v).val =
      (lieFieldTestEquiv k F A ρ τ t).val * (lieFieldTestEquiv k F A ρ τ u).val := by
  change A.baseChangePointsEquiv (fieldBaseMap k F) _ v.val = _
  rw [hv]
  exact (A.baseChangePointsMulEquiv (fieldBaseMap k F) _).map_mul t.val u.val

theorem lieFieldTestEquiv_scalar (c : F)
    (t u : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.LieEigenpoints (A.pullback (fieldBaseMap k F)) (ρ.pullback (fieldBaseMap k F)) τ)
    (hu : u.val = AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar F c ≫ t.val) :
    (lieFieldTestEquiv k F A ρ τ u).val =
      extendedDualScalar k F c ≫ (lieFieldTestEquiv k F A ρ τ t).val := by
  change A.baseChangePointsEquiv (fieldBaseMap k F) _ u.val = _
  rw [hu]
  exact A.baseChangePointsEquiv_precomp (fieldBaseMap k F) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar F c) t.val

theorem hasLieRank_of_extended (r : ℕ)
    (e : (Fin r → F) ≃ extendedLieEigenpoints k F A ρ τ)
    (hadd : ∀ x y, (e (x + y)).val = (e x).val * (e y).val)
    (hsmul : ∀ (c : F) x, (e (c • x)).val = extendedDualScalar k F c ≫ (e x).val) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (A.pullback (fieldBaseMap k F)) (ρ.pullback (fieldBaseMap k F)) τ r := by
  refine ⟨e.trans (lieFieldTestEquiv k F A ρ τ).symm, ?_, ?_⟩
  · intro x y
    apply (A.baseChangePointsMulEquiv (fieldBaseMap k F) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest F)).injective
    change (A.baseChangePointsMulEquiv (fieldBaseMap k F) _)
      ((A.baseChangePointsMulEquiv (fieldBaseMap k F) _).symm (e (x + y)).val) =
      (A.baseChangePointsMulEquiv (fieldBaseMap k F) _)
        ((A.baseChangePointsMulEquiv (fieldBaseMap k F) _).symm (e x).val *
          (A.baseChangePointsMulEquiv (fieldBaseMap k F) _).symm (e y).val)
    rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact hadd x y
  · intro c x
    apply (A.baseChangePointsEquiv (fieldBaseMap k F) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest F)).injective
    change A.baseChangePointsEquiv (fieldBaseMap k F) _
      ((A.baseChangePointsEquiv (fieldBaseMap k F) _).symm (e (c • x)).val) =
      A.baseChangePointsEquiv (fieldBaseMap k F) _
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar F c ≫ (A.baseChangePointsEquiv (fieldBaseMap k F) _).symm (e x).val)
    rw [A.baseChangePointsEquiv_precomp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hsmul c x

end

end OAI.RepresentationTheory.Theta.Geometric.LieFieldTests
