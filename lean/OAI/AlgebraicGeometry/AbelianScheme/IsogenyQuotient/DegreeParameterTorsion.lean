import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.DegreeBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.PicardKernelTorsion

/-! # Degree Parameter Torsion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.DegreeParameterTorsion.Construction

noncomputable section

/-! The degree on a parameter's base points supplies the uniform norm
degree on all its product families and further restrictions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} {X A : Over S} [GrpObj A] [GeometricallyConnected A.hom]
  (f : X ⟶ A) [IsFinite f.left] [Flat f.left] [LocallyOfFinitePresentation f.left]

theorem parameterProduct_finrank_of_base_degree (d : ℕ) (T : Over S)
    (hd : ∀ t : T.left, Relative.DegreeLoci.Construction.relativeFiniteFlatDegree f (T.hom t) = d)
    (U : Over S) (a : U ⟶ T) (b : (U ⊗ A).left) : (U ◁ f).left.finrank b = d := by
  have hp := Picard.PullbackKernelTorsion.Construction.parameterProductMap_isPullback f U
  have hw : A.hom ((snd U A).left b) = T.hom (a.left ((fst U A).left b)) := by
    exact (congrArg (fun m => m b) (snd U A).w).trans
      ((congrArg (fun m => m b) (fst U A).w).symm.trans
        (congrArg (fun m => m ((fst U A).left b)) a.w).symm)
  exact (Scheme.Hom.finrank_of_isPullback _ _ _ _ hp b).trans
    ((Relative.DegreeLoci.Construction.finiteFlatDegree_eq_base_degree f ((snd U A).left b)).trans
      ((congrArg (Relative.DegreeLoci.Construction.relativeFiniteFlatDegree f) hw).trans (hd _)))

set_option backward.isDefEq.respectTransparency false in
theorem canonicalPicardKernel_pow_of_base_degree {S : Scheme.{u}} {g : ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {X : Over S} [GrpObj X]
    (f : X ⟶ A.scheme) [IsMonHom f] [IsFinite f.left] [Flat f.left] [LocallyOfFinitePresentation f.left]
    (d : ℕ) (T : Over S) (hd : ∀ t : T.left, Relative.DegreeLoci.Construction.relativeFiniteFlatDegree f (T.hom t) = d)
    (z : T ⟶ (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme)
    (hz : Canonical.PicardPullback.Construction.canonicalPicardPullbackHom D f T z = 1) : z ^ d = 1 :=
  Parameter.PicardKernelTorsion.Construction.canonicalPicardPullback_kernel_pow_on_parameter D f d T
    (fun U _ a b => parameterProduct_finrank_of_base_degree f d T hd U a b) z hz

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.DegreeParameterTorsion.Construction
