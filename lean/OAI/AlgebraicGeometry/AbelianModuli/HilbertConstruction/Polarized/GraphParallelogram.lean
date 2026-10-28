import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.Parallelogram
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.GraphBundles

/-! # Graph Parallelogram -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The sum and difference pullbacks of a polarized automorphism's canonical bundle have tensor product equal to its fourth power. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_parallelogram {T : Over (Spec (.of K))}
    (a b : T ⟶ A.abelian.scheme) :
    Nonempty (((A.graphBundle.pullback (a * b).left).tensor
      (A.graphBundle.pullback (a * b⁻¹).left)).sheaf ≅
      (((A.graphBundle.pullback a.left).tensorPower 2).tensor
        ((A.graphBundle.pullback b.left).tensorPower 2)).sheaf) :=
  PoincareGraph.Parallelogram.poincareGraphBundle_parallelogram_iso A.dual A.polarization.isogeny.hom a b

def Moduli.Isomorphisms.LevelPreservingIso.graphBundle_sum_difference_iso (e : Moduli.Isomorphisms.LevelPreservingIso A A) :
    (((A.graphBundle.pullback (e.abelian.hom * (𝟙 A.abelian.scheme)).left).tensor
      (A.graphBundle.pullback (e.abelian.hom * (𝟙 A.abelian.scheme)⁻¹).left))).sheaf ≅
      (A.graphBundle.tensorPower 4).sheaf := by
  let ei : (A.graphBundle.pullback (𝟙 A.abelian.scheme : A.abelian.scheme ⟶ A.abelian.scheme).left).sheaf ≅
      A.graphBundle.sheaf := (Scheme.Modules.pullbackId A.abelian.scheme.left).app A.graphBundle.sheaf
  exact (A.graphBundle_parallelogram e.abelian.hom (𝟙 A.abelian.scheme)).some ≪≫
    Tensor.Bifunctor.tensorModuleMapIso ((TensorPower.Maps.tensorPowerFunctor A.abelian.scheme.left 2).mapIso e.graphBundleIso)
      ((TensorPower.Maps.tensorPowerFunctor A.abelian.scheme.left 2).mapIso ei) ≪≫
    (A.graphBundle.tensorPowerAddIso 2 2).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
