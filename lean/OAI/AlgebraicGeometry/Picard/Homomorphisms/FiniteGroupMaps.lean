import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteGeometricPoints
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusKernelBaseChange

/-! # Finite Group Maps -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteGroupMaps

noncomputable section

/-! A proper group morphism with finite scheme-theoretic kernel is finite.
The proof controls every geometric fiber, including nonreduced kernels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
variable (f : A ⟶ B) [IsMonHom f]

def kernelPointEquiv (T : Over S) : (T ⟶ Kernel.Construction.kernelScheme f) ≃ Quotient.Construction.kernelPoints f T where
  toFun x := ⟨x ≫ Kernel.Construction.kernelInclusion f, by
    change (x ≫ Kernel.Construction.kernelInclusion f) ≫ f = 1
    rw [Category.assoc, KernelGroup.Construction.kernelInclusion_comp, MonObj.comp_one]⟩
  invFun x := FrobeniusKernelBaseChange.Construction.kernelLift f x.val x.property
  left_inv x := by
    apply (cancel_mono (Kernel.Construction.kernelInclusion f)).mp
    exact FrobeniusKernelBaseChange.Construction.kernelLift_inclusion _ _ _
  right_inv x := Subtype.ext (FrobeniusKernelBaseChange.Construction.kernelLift_inclusion _ _ _)

instance kernel_hom_isProper [IsProper A.hom] [IsSeparated B.hom] :
    IsProper (Kernel.Construction.kernelScheme f).hom := by
  rw [← (Kernel.Construction.kernelInclusion f).w]
  infer_instance

omit [GrpObj A] [GrpObj B] [IsMonHom f] in
theorem groupHom_isProper [IsProper A.hom] [IsSeparated B.hom] : IsProper f.left := by
  have : IsProper (f.left ≫ B.hom) := by rw [f.w]; infer_instance
  exact IsProper.of_comp f.left B.hom

theorem finite_monoidHom_fiber {G H : Type u} [Group G] [Group H]
    (q : G →* H) [Finite q.ker] (y : H) : Finite {x : G // q x = y} := by
  by_cases h : ∃ x, q x = y
  · obtain ⟨x, rfl⟩ := h
    exact Finite.of_equiv _ (q.fiberEquivKer x).symm
  · have : IsEmpty {x : G // q x = y} := ⟨fun x => h ⟨x.val, x.property⟩⟩
    infer_instance

theorem groupHom_finite_geometric_lifts [IsFinite (Kernel.Construction.kernelScheme f).hom]
    {k : Type u} [Field k] [IsAlgClosed k] (y : Spec (.of k) ⟶ B.left) :
    Finite {x : Spec (.of k) ⟶ A.left // x ≫ f.left = y} := by
  let s := y ≫ B.hom
  let y' : Over.mk s ⟶ B := Over.homMk y rfl
  let q := IsMonHom.monoidHom f (Over.mk s)
  have : Finite (Over.mk s ⟶ Kernel.Construction.kernelScheme f) := FiniteGeometricPoints.Construction.finite_overPoints (Kernel.Construction.kernelScheme f) s
  have : Finite q.ker := Finite.of_equiv _ (kernelPointEquiv f (Over.mk s))
  have : Finite {x : Over.mk s ⟶ A // x ≫ f = y'} := finite_monoidHom_fiber q y'
  exact Finite.of_equiv _ (AbelianScheme.FrobeniusKernel.GeometricIsogeny.Construction.overGeometricFiberEquiv f s y')

theorem groupHom_finite_of_finite_kernel
    [IsProper A.hom] [IsSeparated B.hom] [IsFinite (Kernel.Construction.kernelScheme f).hom] : IsFinite f.left := by
  have : IsProper f.left := groupHom_isProper f
  have : LocallyQuasiFinite f.left := by
    apply LocallyQuasiFinite.of_finite_preimage_singleton
    intro y
    have := groupHom_finite_geometric_lifts f (FiniteGeometricPoints.Construction.geometricResiduePoint B.left y)
    exact FiniteGeometricPoints.Construction.finite_preimage_of_finite_geometric_lifts f.left y
  exact (IsFinite.iff_isProper_and_locallyQuasiFinite f.left).mpr ⟨inferInstance, inferInstance⟩

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteGroupMaps
