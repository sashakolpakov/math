import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality

/-! # Charts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.Charts

noncomputable section

/-! Explicit affine charts of relative projective space, compatible with every affine base map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {R A : CommRingCat.{u}}

def affinePointCoefficients (x : Spec R ⟶ S) : Γ(S, ⊤) ⟶ R :=
  x.appTop ≫ (Scheme.ΓSpecIso R).hom

theorem affinePointCoefficients_spec (x : Spec R ⟶ S) :
    Spec.map (affinePointCoefficients x) = x ≫ S.toSpecΓ := by
  change Spec.map (x.appTop ≫ (Scheme.ΓSpecIso R).hom) = _
  rw [Spec.map_comp, SpecMap_ΓSpecIso_hom]
  exact (Scheme.toSpecΓ_naturality x).symm

theorem affinePointCoefficients_comp (φ : R ⟶ A) (x : Spec R ⟶ S) :
    affinePointCoefficients (Spec.map φ ≫ x) = affinePointCoefficients x ≫ φ := by
  change (x.appTop ≫ (Spec.map φ).appTop) ≫ (Scheme.ΓSpecIso A).hom =
    (x.appTop ≫ (Scheme.ΓSpecIso R).hom) ≫ φ
  rw [Category.assoc, Scheme.ΓSpecIso_naturality, Category.assoc]

def affineProjectiveChartMap (x : Spec R ⟶ S) (n : ℕ) :
    (Projective.ProjectivePresentations.affineProjectiveSpace R n).left ⟶ (Projective.ProjectivePresentations.projectiveSpaceOver S n).left :=
  pullback.lift (Projective.CoefficientFunctoriality.polynomialProjectiveMap (affinePointCoefficients x) n)
    ((Projective.ProjectivePresentations.affineProjectiveSpace R n).hom ≫ x) (by
      rw [Projective.CoefficientFunctoriality.polynomialProjectiveMap_over, affinePointCoefficients_spec, Category.assoc])

theorem affineProjectiveChartMap_fst (x : Spec R ⟶ S) (n : ℕ) :
    affineProjectiveChartMap x n ≫
      pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ =
        Projective.CoefficientFunctoriality.polynomialProjectiveMap (affinePointCoefficients x) n :=
  pullback.lift_fst _ _ _

theorem affineProjectiveChartMap_over (x : Spec R ⟶ S) (n : ℕ) :
    affineProjectiveChartMap x n ≫ (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom =
      (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom ≫ x :=
  pullback.lift_snd _ _ _

theorem affineProjectiveChartMap_isPullback (x : Spec R ⟶ S) (n : ℕ) :
    IsPullback (affineProjectiveChartMap x n) (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom
      (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom x := by
  have h := Projective.CoefficientFunctoriality.polynomialProjectiveMap_isPullback (affinePointCoefficients x) n
  rw [affinePointCoefficients_spec] at h
  let p : (Projective.ProjectivePresentations.projectiveSpaceOver S n).left ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).left :=
    pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ
  have hs : IsPullback (affineProjectiveChartMap x n ≫ p)
      (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom
      (x ≫ S.toSpecΓ) := by
    rw [show affineProjectiveChartMap x n ≫ p =
      Projective.CoefficientFunctoriality.polynomialProjectiveMap (affinePointCoefficients x) n from affineProjectiveChartMap_fst x n]
    exact h
  exact hs.of_right (affineProjectiveChartMap_over x n)
    (IsPullback.of_hasPullback (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ)

theorem affineProjectiveChartMap_naturality (φ : R ⟶ A) (x : Spec R ⟶ S) (n : ℕ) :
    Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n ≫ affineProjectiveChartMap x n =
      affineProjectiveChartMap (Spec.map φ ≫ x) n := by
  apply pullback.hom_ext
  · let p : (Projective.ProjectivePresentations.projectiveSpaceOver S n).left ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).left :=
      pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ
    change (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n ≫ affineProjectiveChartMap x n) ≫ p =
      affineProjectiveChartMap (Spec.map φ ≫ x) n ≫ p
    exact (Category.assoc _ _ p).trans
      ((congrArg (fun k => Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n ≫ k) (affineProjectiveChartMap_fst x n)).trans
        ((Projective.CoefficientFunctoriality.polynomialProjectiveMap_comp (affinePointCoefficients x) φ n).symm.trans
          ((congrArg (fun k => Projective.CoefficientFunctoriality.polynomialProjectiveMap k n) (affinePointCoefficients_comp φ x).symm).trans
            (affineProjectiveChartMap_fst (Spec.map φ ≫ x) n).symm)))
  · change (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n ≫ affineProjectiveChartMap x n) ≫
      (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom =
        affineProjectiveChartMap (Spec.map φ ≫ x) n ≫ (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom
    rw [Category.assoc, affineProjectiveChartMap_over, affineProjectiveChartMap_over,
      ← Category.assoc, Projective.CoefficientFunctoriality.polynomialProjectiveMap_over, Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.Charts
