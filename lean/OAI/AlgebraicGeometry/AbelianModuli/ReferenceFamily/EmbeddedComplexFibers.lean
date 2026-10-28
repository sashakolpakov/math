import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange

/-! # Embedded Complex Fibers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedComplexFibers

noncomputable section

/-! A retained affine projective embedding constructs the native
projective presentation of every actual complex fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def projectivePresentationOfAffineEmbedding {R : Type} [CommRing R]
    {X : Over (Spec (.of R))} (n : ℕ) (i : X ⟶ HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n)
    [IsClosedImmersion i.left] : HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X where
  dimension := n
  embedding := i ≫ (HilbertConstruction.Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) n).inv
  closedImmersion := by
    have : IsIso (HilbertConstruction.Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) n).inv.left :=
      ((Over.forget (Spec (.of R))).mapIso (HilbertConstruction.Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) n)).isIso_inv
    exact inferInstanceAs (IsClosedImmersion (i.left ≫ (HilbertConstruction.Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) n).inv.left))

def embeddedComplexFiberProjectivePresentation {R : Type} [CommRing R] {g : ℕ}
    (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of R))) (n : ℕ)
    (i : A.scheme ⟶ HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n) [IsClosedImmersion i.left]
    (q : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (.of R)) :
    Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.pullback q).scheme.left (A.pullback q).scheme.hom := by
  let r := Spec.preimage q
  have hr : Spec.map r = q := Spec.map_preimage q
  let : Algebra R ℂ := r.hom.toAlgebra
  let F := Over.pullback q
  let eP : F.obj (HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n) ≅ HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace ℂ n :=
    eqToIso (congrArg (fun f => (Over.pullback f).obj (HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n)) hr.symm) ≪≫
    (HilbertConstruction.Projective.SpaceBaseChange.affineProjectiveSpaceBaseChangeIso (R := R) (A := ℂ) n).symm
  have : IsIso eP.hom.left := ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso eP).isIso_hom
  have : IsClosedImmersion (F.map i).left :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion) q i inferInstance
  let j : (A.pullback q).scheme ⟶ HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace ℂ n := F.map i ≫ eP.hom
  have : IsClosedImmersion j.left :=
    inferInstanceAs (IsClosedImmersion ((F.map i).left ≫ eP.hom.left))
  exact Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.nativeProjectivePresentation (projectivePresentationOfAffineEmbedding n j)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedComplexFibers
