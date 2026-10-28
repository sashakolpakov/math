import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CompositePointedCancellation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.UniversalPointedFieldDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.UniversalGlobalFunctions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Products

/-! # Finite Target Field Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.FiniteTargetFieldDetection

noncomputable section

/-! Pointed maps into a group family finite over a fixed Noetherian
abelian family are detected on fields, on arbitrary affine test schemes.
The finite target family itself need not descend to the Noetherian base. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {S : Scheme.{u}} [IsNoetherian S] {g h : ℕ}
variable (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
variable (PA : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (PB : Projective.ProjectivePresentations.ProjectivePresentation B.scheme)
variable (T : Over S) [IsAffine T.left]
variable (D : Over T.left) [GrpObj D]
variable (r : D ⟶ (B.pullback T.hom).scheme) [IsMonHom r] [IsFinite r.left]

include PA PB r in
theorem relativeFiniteTarget_pointedMap_eq_of_fieldPullbacks
    (f q : (A.pullback T.hom).scheme ⟶ D)
    (hf : η[(A.pullback T.hom).scheme] ≫ f = η[D])
    (hq : η[(A.pullback T.hom).scheme] ≫ q = η[D])
    (he : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ T.left),
      (Over.pullback s).map f = (Over.pullback s).map q) : f = q := by
  let Q := PA.product PB
  have hc : f ≫ r = q ≫ r := by
    refine UniversalPointedFieldDetection.relativeUniversalPointedMap_eq_of_fieldPullbacks A B Q.embedding T (f ≫ r) (q ≫ r)
      ((Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ r) hf).trans (IsMonHom.one_hom r)))
      ((Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ r) hq).trans (IsMonHom.one_hom r))) ?_
    intro K _ s
    rw [Functor.map_comp, Functor.map_comp, he K s]
  let : IsIso (A.pullback T.hom).scheme.hom.appTop :=
    Projective.UniversalGlobalFunctions.projectivePresentation_baseChange_globalFunctions_isIso PA η[A.scheme].left η[A.scheme].w
      (IsPullback.of_hasPullback A.scheme.hom T.hom)
  exact Finite.CompositePointedCancellation.pointed_maps_eq_of_finite_composite r f q hf hq hc

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.FiniteTargetFieldDetection
