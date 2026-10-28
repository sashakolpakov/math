import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Kernels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TypeKernelSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TypeFromAffineSections

/-! # Quasicoherent Kernels -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.QuasicoherentKernels

noncomputable section

/-! Kernels of quasicoherent finite-type sheaves over locally Noetherian schemes remain quasicoherent and finite type. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem noetherian_quasicoherent_kernel_finiteType {X : Scheme.{u}} [IsLocallyNoetherian X]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] [M.IsFiniteType]
    (f : M ⟶ N) : (kernel f).IsFiniteType := by
  have : (kernel f).IsQuasicoherent := Quasicoherent.Kernels.module_quasicoherent_kernel f
  exact Finite.TypeFromAffineSections.module_finiteType_of_affine_sections_finite (kernel f) (Finite.TypeKernelSections.affineOpen_kernel_sections_finite f)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.QuasicoherentKernels
