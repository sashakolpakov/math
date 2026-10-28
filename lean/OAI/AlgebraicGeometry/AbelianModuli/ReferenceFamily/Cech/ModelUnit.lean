import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GlobalModel

/-! # Model Unit -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ModelUnit.CechModelUnit

noncomputable section

/-! The actual constant function one defines a degree-zero cycle and
a unit map in any Cech model of the structure sheaf. Its differential
vanishes over the original base ring. -/

universe u
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S)
  {I : Type u} [LinearOrder I] (U : I → X.Opens) (hU : iSup U = ⊤)
  {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
  (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex f (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) U) [QuasiIsoAt φ 0]

def cycle : (D.d 0 1).hom.ker :=
  (Quotients.FiniteDescent.GlobalModel.Construction.GlobalModelSections.equiv f (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) U hU φ).symm (1 : Γ(X, ⊤))

def unitMap : Γ(S, ⊤) →ₗ[Γ(S, ⊤)] D.X 0 :=
  LinearMap.toSpanSingleton Γ(S, ⊤) (D.X 0) (cycle f U hU φ).val

theorem unitMap_apply (r : Γ(S, ⊤)) :
    unitMap f U hU φ r = r • (cycle f U hU φ).val := rfl

theorem unitMap_one : unitMap f U hU φ 1 = (cycle f U hU φ).val := by
  rw [unitMap_apply, one_smul]

theorem differential_unitMap : (D.d 0 1).hom.comp (unitMap f U hU φ) = 0 := by
  apply LinearMap.ext
  intro r
  change (D.d 0 1) (r • (cycle f U hU φ).val) = 0
  rw [(D.d 0 1).hom.map_smul, (cycle f U hU φ).property, smul_zero]

theorem cycle_section :
    Quotients.FiniteDescent.GlobalModel.Construction.GlobalModelSections.equiv f (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) U hU φ (cycle f U hU φ) = (1 : Γ(X, ⊤)) :=
  (Quotients.FiniteDescent.GlobalModel.Construction.GlobalModelSections.equiv f (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) U hU φ).apply_symm_apply _

theorem cycle_coordinate :
    φ.f 0 (cycle f U hU φ).val = Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map f (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) U (1 : Γ(X, ⊤)) := by
  rw [Quotients.FiniteDescent.GlobalModel.Construction.GlobalModelSections.coordinate f (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) U hU φ, cycle_section]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ModelUnit.CechModelUnit
