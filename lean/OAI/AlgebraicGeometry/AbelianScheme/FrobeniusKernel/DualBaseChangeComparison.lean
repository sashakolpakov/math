import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BaseChange

/-! # Dual Base Change Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualBaseChangeComparison

noncomputable section

/-! The original HilbertConstruction dual pullback retains the same native Poincare
representation as the dimension-independent source-base-change construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace Construction

attribute [local instance] BaseChange.Construction.pulledBackGroup

variable {S S' : Scheme} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}

def nativePullbackDualPicardData (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (s : S' ⟶ S) :
    Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData ((Over.pullback s).obj A.scheme) :=
  ((Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).pullback s).withPicardGroup

def originalPullbackDualPicardData (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (s : S' ⟶ S) :
    Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData ((Over.pullback s).obj A.scheme) :=
  (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled (D.pullback s)).withPicardGroup

theorem nativeDualData_ofBundled_pullback (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (s : S' ⟶ S) :
    Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled (D.pullback s) = (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).pullback s := by
  rfl

theorem nativeDualRepresentable_ofBundled_pullback (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (s : S' ⟶ S) :
    (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled (D.pullback s)).representable =
      ((Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).pullback s).representable := rfl

theorem nativeDualPicardPoint_ofBundled_pullback (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (s : S' ⟶ S)
    (T : Over S') (q : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf ((Over.pullback s).obj A.scheme)).obj.obj (.op T)) :
    (@Functor.RepresentableBy.homEquiv (Over S') _
      (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf ((Over.pullback s).obj A.scheme)).obj
      ((Over.pullback s).obj D.abelian.scheme)
      (nativePullbackDualPicardData D s).representable T).symm q =
      (@Functor.RepresentableBy.homEquiv (Over S') _
        (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf ((Over.pullback s).obj A.scheme)).obj
        ((Over.pullback s).obj D.abelian.scheme)
        (originalPullbackDualPicardData D s).representable T).symm q := by
  exact congrArg (fun r : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf ((Over.pullback s).obj A.scheme)).obj.RepresentableBy
    ((Over.pullback s).obj D.abelian.scheme) => (r.homEquiv (X := T)).symm q)
    (nativeDualRepresentable_ofBundled_pullback D s).symm

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualBaseChangeComparison
