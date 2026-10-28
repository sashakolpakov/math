import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechModelSections

/-! # Global Model -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.GlobalModel

noncomputable section

/-! Global sections and their coordinates in a degree-zero Cech model. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.GlobalModelSections

variable {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
variable {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
variable (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U) [QuasiIsoAt φ 0]

def equiv : (D.d 0 1).hom.ker ≃ₗ[Γ(S, ⊤)] (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op ⊤) :=
  (CochainZero.Construction.CochainZeroCycles.kernelEquiv φ).trans
    (OrderedCechZeroGluing.Construction.OrderedCechZeroCoordinates.sectionsEquiv π M U hU).symm

theorem coordinate (x : (D.d 0 1).hom.ker) :
    φ.f 0 x.val = OrderedCechSquare.Construction.OrderedCechAugmentation.map π M U (equiv π M U hU φ x) := by
  let e := OrderedCechZeroGluing.Construction.OrderedCechZeroCoordinates.sectionsEquiv π M U hU
  let k := CochainZero.Construction.CochainZeroCycles.kernelEquiv φ
  have he := congrArg Subtype.val (e.apply_symm_apply (k x))
  exact (CochainZero.Construction.CochainZeroCycles.kernelEquiv_apply_val φ x).symm.trans he.symm

end Construction.GlobalModelSections

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.GlobalModel
