import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELGeometricKernelType
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELQuotientBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CharZeroFieldParameters

/-! # PEL Kernel Module Type -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELKernelModuleType

noncomputable section

/-! Swapping paired PEL quotients preserves the full TorsionQuotient kernel
module-type condition at every geometric point of an arbitrary test
base. The type comparison is proved after the actual field pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CharZeroFieldParameters.Construction

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [CharZero K]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T : Over (Spec (.of K))} {A B : PEL.Objects.PELObject P iota N T}

theorem pairedPELQuotient_kernel_type_at_geometric_point
    (f : PELQuotients.PairedPELQuotient A B n) (hn : 0 < n)
    (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2))
    (k : Type) [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ T.left) :
    Nonempty (f.forward.isogeny.kernelAt (Over.mk b) ≃*
      f.reverse.isogeny.kernelAt (Over.mk b)) := by
  let : CharZero k := AbelianScheme.IsogenyQuotient.CharZeroFieldParameters.Construction.field_charZero_of_map_to_charZero_field (b ≫ T.hom)
  let u : Over.mk (b ≫ T.hom) ⟶ T := Over.homMk b rfl
  obtain ⟨e⟩ := PELGeometricKernelType.pairedPELQuotient_geometric_kernel_type (f.pullback u) hn hdegree
  have eq : (f.forward.isogeny.pullback b).kernelAt (Over.mk (𝟙 (Spec (.of k)))) ≃*
      f.forward.isogeny.kernelAt (Over.mk b) := by
    have h := f.forward.isogeny.kernelBaseChangeEquiv b (Over.mk (𝟙 (Spec (.of k))))
    change (f.forward.isogeny.pullback b).kernelAt (Over.mk (𝟙 (Spec (.of k)))) ≃*
      f.forward.isogeny.kernelAt (Over.mk (𝟙 (Spec (.of k)) ≫ b)) at h
    erw [Category.id_comp] at h
    exact h
  have ev : (f.reverse.isogeny.pullback b).kernelAt (Over.mk (𝟙 (Spec (.of k)))) ≃*
      f.reverse.isogeny.kernelAt (Over.mk b) := by
    have h := f.reverse.isogeny.kernelBaseChangeEquiv b (Over.mk (𝟙 (Spec (.of k))))
    change (f.reverse.isogeny.pullback b).kernelAt (Over.mk (𝟙 (Spec (.of k)))) ≃*
      f.reverse.isogeny.kernelAt (Over.mk (𝟙 (Spec (.of k)) ≫ b)) at h
    erw [Category.id_comp] at h
    exact h
  exact ⟨eq.symm.trans (e.trans ev)⟩

theorem pairedPELQuotient_kernel_moduleType_iff
    (f : PELQuotients.PairedPELQuotient A B n) (hn : 0 < n)
    (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2))
    (M : Type) [AddCommGroup M] :
    (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.forward.isogeny.hom).HasModuleType M ↔
      (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.reverse.isogeny.hom).HasModuleType M := by
  constructor
  · intro h k _ _ b t
    obtain ⟨e⟩ := pairedPELQuotient_kernel_type_at_geometric_point f hn hdegree k b
    obtain ⟨d⟩ := h k b t
    exact ⟨e.symm.trans d⟩
  · intro h k _ _ b t
    obtain ⟨e⟩ := pairedPELQuotient_kernel_type_at_geometric_point f hn hdegree k b
    obtain ⟨d⟩ := h k b t
    exact ⟨e.trans d⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELKernelModuleType
