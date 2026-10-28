import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GeometricIsogeny
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
import Mathlib.Topology.Connected.TotallyDisconnected

/-! # Finite Target Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteTargetRigidity.Construction

noncomputable section

/-!
Maps from a connected reduced geometric scheme to a finite scheme are
determined by one point. This retains nonreduced finite targets and is the
rigidity calculation needed when comparing maps through finite kernels.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]

omit [IsAlgClosed K] in
theorem finiteOverField_discrete {Y : Scheme.{u}} (p : Y ⟶ Spec (.of K)) [IsFinite p] :
    DiscreteTopology Y := by
  have h := p.isDiscrete_preimage_singleton (IsLocalRing.closedPoint K)
  have he : p ⁻¹' {IsLocalRing.closedPoint K} = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  exact isDiscrete_univ_iff.mp ((congrArg IsDiscrete he).mp h)

/-- Reducedness of the source, rather than reducedness of the finite
target, upgrades equality of underlying point maps to scheme equality. -/
theorem finiteTargetHom_ext {X Y : Over (Spec (.of K))}
    [IsReduced X.left] [LocallyOfFiniteType X.hom] [PreconnectedSpace X.left]
    [IsFinite Y.hom] (a b : X ⟶ Y) (x₀ : X.left) (h₀ : a.left x₀ = b.left x₀) : a = b := by
  have : DiscreteTopology Y.left := finiteOverField_discrete Y.hom
  have : LocallyOfFiniteType (a.left ≫ Y.hom) := (congrArg LocallyOfFiniteType a.w).mpr inferInstance
  apply Over.OverMorphism.ext
  apply ext_of_apply_eq Y.hom Set.univ isOpen_univ.isLocallyClosed dense_univ
  · intro x _ _
    exact (PreconnectedSpace.constant (inferInstanceAs (PreconnectedSpace X.left))
      a.left.continuous (x := x) (y := x₀)).trans
        (h₀.trans (PreconnectedSpace.constant (inferInstanceAs (PreconnectedSpace X.left))
          b.left.continuous (x := x) (y := x₀)).symm)
  · exact a.w.trans b.w.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteTargetRigidity.Construction
