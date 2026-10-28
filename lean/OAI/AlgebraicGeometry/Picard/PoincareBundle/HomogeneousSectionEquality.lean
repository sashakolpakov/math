import OAI.AlgebraicGeometry.Picard.PoincareBundle.Homogeneous

/-! # Homogeneous Section Equality -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.HomogeneousSectionEquality

noncomputable section

/-! Forgetting homogeneity retains equality of the actual relative Picard sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Homogeneous OAI.AlgebraicGeometry.Picard.PoincareBundle.Functor

variable {S : Scheme.{u}} (A : Over S) [GrpObj A]

/-- Forget only the proof of translation invariance of the actual line class. -/
def inclusion : Homogeneous.homogeneousPresheaf A ⟶ Functor.relativePicardPresheaf A where
  app _T := ↾(fun q => q.val)
  naturality {_T _U} _f := rfl

/-- The same forgetful map on fppf sheafifications. -/
def sheafInclusion : Homogeneous.homogeneousSheaf A ⟶ Functor.relativePicardSheaf A :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map (inclusion A)

/-- The forgetful map retains the original line class after sheafification. -/
theorem inclusion_section {T : Over S} (q : (Homogeneous.homogeneousPresheaf A).obj (op T)) :
    (sheafInclusion A).hom.app (op T)
      ((toSheafify (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf A)).app (op T) q) =
      (Functor.toRelativePicard A).app (op T) q.val :=
  (congrArg (fun t => t.app (op T) q)
    (toSheafify_naturality (Scheme.fppfTopology.over S) (inclusion A))).symm

/-- Equality of homogeneous sections is equality of the underlying relative Picard sections. -/
theorem relative_eq {T : Over S} (q r : (Homogeneous.homogeneousPresheaf A).obj (op T))
    (h : (toSheafify (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf A)).app (op T) q =
      (toSheafify (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf A)).app (op T) r) :
    (Functor.toRelativePicard A).app (op T) q.val = (Functor.toRelativePicard A).app (op T) r.val :=
  (inclusion_section A q).symm.trans
    ((congrArg ((sheafInclusion A).hom.app (op T)) h).trans (inclusion_section A r))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.HomogeneousSectionEquality
