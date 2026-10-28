import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientPullback

/-! # Space Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange

noncomputable section

/-! HilbertConstruction's standard projective spaces commute with arbitrary affine and scheme base changes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

def affineProjectiveSpaceBaseChangeIso (n : ℕ) :
    ProjectivePresentations.affineProjectiveSpace A n ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj (ProjectivePresentations.affineProjectiveSpace R n) :=
  Over.isoMk (CoefficientPullback.polynomialProjectiveCoefficient_isPullback (R := R) (A := A) (n := n)).isoPullback
    (CoefficientPullback.polynomialProjectiveCoefficient_isPullback (R := R) (A := A) (n := n)).isoPullback_hom_snd

theorem affineProjectiveSpaceBaseChangeIso_hom_fst (n : ℕ) :
    (affineProjectiveSpaceBaseChangeIso (R := R) (A := A) n).hom.left ≫
      CategoryTheory.Limits.pullback.fst (ProjectivePresentations.affineProjectiveSpace R n).hom
        (Spec.map (CommRingCat.ofHom (algebraMap R A))) =
          Polynomial.ProjectiveCoefficients.polynomialProjectiveCoefficientMap (R := R) (A := A) (n := n) :=
  (CoefficientPullback.polynomialProjectiveCoefficient_isPullback (R := R) (A := A) (n := n)).isoPullback_hom_fst

def projectiveSpaceOverBaseChangeIso {S T : Scheme.{u}} (f : T ⟶ S) (n : ℕ) :
    ProjectivePresentations.projectiveSpaceOver T n ≅ (Over.pullback f).obj (ProjectivePresentations.projectiveSpaceOver S n) := by
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := f.appTop.hom.toAlgebra
  let P := ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n
  exact (Over.pullback T.toSpecΓ).mapIso
      (affineProjectiveSpaceBaseChangeIso (R := Γ(S, ⊤)) (A := Γ(T, ⊤)) n) ≪≫
    (Over.pullbackComp T.toSpecΓ (Spec.map f.appTop)).symm.app P ≪≫
    eqToIso (congrArg (fun h : T ⟶ Spec Γ(S, ⊤) => (Over.pullback h).obj P)
      (Scheme.toSpecΓ_naturality f).symm) ≪≫
    (Over.pullbackComp f S.toSpecΓ).app P

def projectiveSpaceOverSpecIso (R : CommRingCat.{u}) (n : ℕ) :
    ProjectivePresentations.projectiveSpaceOver (Spec R) n ≅ ProjectivePresentations.affineProjectiveSpace R n := by
  let : Algebra Γ(Spec R, ⊤) R := (Scheme.ΓSpecIso R).hom.hom.toAlgebra
  exact eqToIso (congrArg (fun h : Spec R ⟶ Spec Γ(Spec R, ⊤) =>
    (Over.pullback h).obj (ProjectivePresentations.affineProjectiveSpace Γ(Spec R, ⊤) n))
      (SpecMap_ΓSpecIso_hom R).symm) ≪≫
    (affineProjectiveSpaceBaseChangeIso (R := Γ(Spec R, ⊤)) (A := R) n).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange
