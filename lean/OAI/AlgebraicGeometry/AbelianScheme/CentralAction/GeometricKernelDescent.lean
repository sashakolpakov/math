import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.GroupKernel
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Quotient
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Etale

/-! # Geometric Kernel Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.GeometricKernelDescent.Construction

noncomputable section

/-! Over an algebraically closed field, equality of geometric kernels
of etale isogenies is equality of the full subgroup functors, including
all nonreduced test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k]

theorem over_hom_ext_rational {X Y : Over (Spec (.of k))}
    [IsReduced X.left] [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated Y.hom]
    (f g : X ⟶ Y)
    (h : ∀ x : Over.mk (𝟙 (Spec (.of k))) ⟶ X, x ≫ f = x ≫ g) : f = g := by
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  apply Over.OverMorphism.ext
  apply ext_of_apply_eq Y.hom Set.univ isOpen_univ.isLocallyClosed dense_univ
  · intro x _ hx
    let p : Over.mk (𝟙 (Spec (.of k))) ⟶ X :=
      Over.homMk (pointOfClosedPoint X.hom x hx) (pointOfClosedPoint_comp X.hom x hx)
    have he := congrArg (fun z => z.left (default : Spec (.of k))) (h p)
    change f.left (pointOfClosedPoint X.hom x hx default) =
      g.left (pointOfClosedPoint X.hom x hx default) at he
    simpa only [pointOfClosedPoint_apply] using he
  · exact f.w.trans g.w.symm

variable {A B C : Over (Spec (.of k))} [GrpObj A] [GrpObj B] [GrpObj C]

omit [GrpObj A] in
/-- Geometric kernel inclusion extends to all test schemes because the
actual kernel scheme is reduced, not because the tests are reduced. -/
theorem kernel_inclusion_all_tests_of_geometric
    (f : A ⟶ B) (g : A ⟶ C)
    [IsFinite (GroupKernel.Construction.groupKernelScheme f).hom] [Etale (GroupKernel.Construction.groupKernelScheme f).hom]
    [LocallyOfFiniteType C.hom] [IsSeparated C.hom]
    (h : ∀ x : Over.mk (𝟙 (Spec (.of k))) ⟶ A, x ≫ f = 1 → x ≫ g = 1)
    (T : Over (Spec (.of k))) (x : T ⟶ A) (hx : x ≫ f = 1) : x ≫ g = 1 := by
  have : IsReduced (GroupKernel.Construction.groupKernelScheme f).left :=
    TateComparison.Etale.etale_source_reduced (GroupKernel.Construction.groupKernelScheme f).hom
  have hi : GroupKernel.Construction.groupKernelInclusion f ≫ g = (1 : GroupKernel.Construction.groupKernelScheme f ⟶ C) := by
    apply over_hom_ext_rational
    intro z
    have hz := h (z ≫ GroupKernel.Construction.groupKernelInclusion f) ((GroupKernel.Construction.groupKernelPointsEquiv f _ z).property)
    simpa only [Category.assoc, MonObj.comp_one] using hz
  calc
    x ≫ g = (GroupKernel.Construction.groupKernelLift f x hx ≫ GroupKernel.Construction.groupKernelInclusion f) ≫ g := by
      rw [GroupKernel.Construction.groupKernelLift_inclusion]
    _ = 1 := by rw [Category.assoc, hi, MonObj.comp_one]

omit [GrpObj A] in
theorem kernel_eq_all_tests_of_geometric
    (f : A ⟶ B) (g : A ⟶ C)
    [IsFinite (GroupKernel.Construction.groupKernelScheme f).hom] [Etale (GroupKernel.Construction.groupKernelScheme f).hom]
    [IsFinite (GroupKernel.Construction.groupKernelScheme g).hom] [Etale (GroupKernel.Construction.groupKernelScheme g).hom]
    [LocallyOfFiniteType B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType C.hom] [IsSeparated C.hom]
    (h : ∀ x : Over.mk (𝟙 (Spec (.of k))) ⟶ A, x ≫ f = 1 ↔ x ≫ g = 1)
    (T : Over (Spec (.of k))) (x : T ⟶ A) : x ≫ f = 1 ↔ x ≫ g = 1 :=
  ⟨kernel_inclusion_all_tests_of_geometric f g (fun z => (h z).mp) T x,
    kernel_inclusion_all_tests_of_geometric g f (fun z => (h z).mpr) T x⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.GeometricKernelDescent.Construction
