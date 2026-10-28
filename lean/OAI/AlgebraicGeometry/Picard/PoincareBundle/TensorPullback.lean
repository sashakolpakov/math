import OAI.AlgebraicGeometry.Picard.PoincareBundle.TensorCongruence

/-! # Tensor Pullback -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TensorPullback

noncomputable section

/-! Actual homogeneous tensor products commute with represented Picard pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Functor OAI.AlgebraicGeometry.Picard.PoincareBundle.Homogeneous OAI.AlgebraicGeometry.Picard.PoincareBundle.TensorCongruence

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f]

/-- Geometric tensor pullback induces the tensor equation in the homogeneous presheaf. -/
theorem tensorHomogeneous_pullback {T : Over S} (q r : (Homogeneous.homogeneousPresheaf B).obj (op T)) :
    (Homogeneous.pullbackHomogeneousPresheaf f).app (op T) (TensorCongruence.tensorHomogeneous B q r) =
      TensorCongruence.tensorHomogeneous A ((Homogeneous.pullbackHomogeneousPresheaf f).app (op T) q)
        ((Homogeneous.pullbackHomogeneousPresheaf f).app (op T) r) := by
  apply Subtype.ext
  exact Tensor.LineBundles.tensorClass_pullback (Functor.familyMap f T) q.val r.val

/-- The sheaf pullback of an actual homogeneous class is its geometric presheaf pullback followed by sheafification. -/
theorem toSheafify_pullback {T : Over S} (q : (Homogeneous.homogeneousPresheaf B).obj (op T)) :
    (Homogeneous.pullbackHomogeneousSheaf f).hom.app (op T)
        ((toSheafify (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf B)).app (op T) q) =
      (toSheafify (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf A)).app (op T)
        ((Homogeneous.pullbackHomogeneousPresheaf f).app (op T) q) :=
  (congrArg (fun t => t.app (op T) q)
    (toSheafify_naturality (Scheme.fppfTopology.over S) (Homogeneous.pullbackHomogeneousPresheaf f))).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TensorPullback
