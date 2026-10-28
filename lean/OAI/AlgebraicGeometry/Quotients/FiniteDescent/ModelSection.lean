import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechModelSections
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FieldTensor
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FieldPoint

/-! # Model Section -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModelSection

noncomputable section

/-! Nonzero sections at a field-valued point are detected by the support
of a finite module built from the first differential of a Cech model. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.ModelSectionSupport

variable {X Y S : Scheme.{u}} {K : Type u} [Field K]
variable (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ Spec (.of K)) (g : Spec (.of K) ⟶ S)
variable (h : f ≫ π = ρ ≫ g) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
variable {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
variable (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U)
variable [QuasiIsoAt (CechModelBaseChange.Construction.CechBaseChangeMap.modelMap f π ρ g h M U φ) 0]
variable [Module.Finite Γ(S, ⊤) (D.X 0)] [Module.Projective Γ(S, ⊤) (D.X 0)]
variable [Module.Finite Γ(S, ⊤) (D.X 1)] [Module.Projective Γ(S, ⊤) (D.X 1)]

include φ h hU

theorem sections_iff (t : Spec (.of K)) :
    Nontrivial Γ((Scheme.Modules.pullback f).obj M, ⊤) ↔
      S.toSpecΓ (g t) ∈ Module.support Γ(S, ⊤) (KernelSupportIs.Construction.KernelSupport.dualCokernel (D.d 0 1).hom) := by
  let : Field Γ(Spec (.of K), ⊤) := FieldPoint.Construction.FieldPointPrime.sectionsField K
  let : Algebra Γ(S, ⊤) Γ(Spec (.of K), ⊤) := g.appTop.hom.toAlgebra
  have he := (CechModelSections.Construction.CechBaseChangeMap.kernelSections f π ρ g h M U hU φ).nontrivial_congr.symm
  have hd := KernelSupportIs.Construction.KernelSupport.field_kernel_iff Γ(Spec (.of K), ⊤) (D.d 0 1).hom
  have hp := FieldTensor.Construction.FieldTensorSupport.nontrivial_iff Γ(Spec (.of K), ⊤)
    (KernelSupportIs.Construction.KernelSupport.dualCokernel (D.d 0 1).hom) (S.toSpecΓ (g t)) (FieldPoint.Construction.FieldPointPrime.kernel g t)
  exact he.trans (hd.trans hp)

end Construction.ModelSectionSupport

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModelSection
