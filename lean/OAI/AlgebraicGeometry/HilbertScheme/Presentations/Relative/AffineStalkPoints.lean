import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffinePoints

/-! # Affine Stalk Points -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffineStalkPoints

noncomputable section

/-! The affine adjunction followed by the stalk germ, before specializing its rings. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable (R : CommRingCat.{u}) (T : Over (Spec R))

@[instance_reducible]
def relativeStalkAlgebra (t : T.left) : Algebra R (T.left.presheaf.stalk t) :=
  ((T.left.presheaf.Γgerm t).hom.comp (algebraMap R (AffinePoints.relativeGlobalAlgebra R T))).toAlgebra

def relativeGlobalToStalk (t : T.left) :
    letI := relativeStalkAlgebra R T t
    AffinePoints.relativeGlobalAlgebra R T →ₐ[R] T.left.presheaf.stalk t := by
  letI := relativeStalkAlgebra R T t
  exact { __ := (T.left.presheaf.Γgerm t).hom, commutes' := fun _ => rfl }

variable (A : Type u) [CommRing A] [Algebra R A]

def relativeAffinePointStalkMap (x : T ⟶ AffinePoints.relativeAffineScheme R A) (t : T.left) :
    letI := relativeStalkAlgebra R T t
    A →ₐ[R] T.left.presheaf.stalk t := by
  letI := relativeStalkAlgebra R T t
  exact (relativeGlobalToStalk R T t).comp (AffinePoints.relativeAffinePointEquiv R A T x)

theorem relativeAffinePointStalkMap_postcomp
    {B : Type u} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (x : T ⟶ AffinePoints.relativeAffineScheme R B) (t : T.left) :
    letI := relativeStalkAlgebra R T t
    relativeAffinePointStalkMap R T A (x ≫ (algSpec R).map (CommAlgCat.ofHom φ).op) t =
      (relativeAffinePointStalkMap R T B x t).comp φ := by
  let := relativeStalkAlgebra R T t
  exact (congrArg ((relativeGlobalToStalk R T t).comp)
    (AffinePoints.relativeAffinePointEquiv_postcomp R A φ x)).trans
      (AlgHom.comp_assoc (relativeGlobalToStalk R T t) (AffinePoints.relativeAffinePointEquiv R B T x) φ)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffineStalkPoints
