import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.ShortComplexHomotopy

/-! # Short Complex Last Cokernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ShortComplexLastCokernel

noncomputable section

/-! Endpoint-controlled short-complex homotopies preserve the last cokernel. Reversing a homotopy with zero first endpoint supplies exactly the required control for the dual augmentation. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u v
variable {V : Type u} [Category.{v} V] [Abelian V]
  {S T U : ShortComplex V}

def shortComplexLastCokernelMap (φ : S ⟶ T) : cokernel S.g ⟶ cokernel T.g :=
  cokernel.desc S.g (φ.τ₃ ≫ cokernel.π T.g) (by
    rw [← Category.assoc, ← φ.comm₂₃, Category.assoc, cokernel.condition, comp_zero])

@[reassoc (attr := simp)]
theorem shortComplexLastCokernelMap_fac (φ : S ⟶ T) :
    cokernel.π S.g ≫ shortComplexLastCokernelMap φ = φ.τ₃ ≫ cokernel.π T.g :=
  cokernel.π_desc _ _ _

theorem shortComplexLastCokernelMap_id : shortComplexLastCokernelMap (𝟙 S) = 𝟙 _ := by
  apply (cancel_epi (cokernel.π S.g)).mp
  simp

theorem shortComplexLastCokernelMap_comp (φ : S ⟶ T) (ψ : T ⟶ U) :
    shortComplexLastCokernelMap (φ ≫ ψ) = shortComplexLastCokernelMap φ ≫ shortComplexLastCokernelMap ψ := by
  apply (cancel_epi (cokernel.π S.g)).mp
  simp [Category.assoc]

theorem shortComplexLastCokernelMap_homotopy {φ ψ : S ⟶ T}
    (h : ShortComplex.Homotopy φ ψ) (h₃ : h.h₃ = 0) :
    shortComplexLastCokernelMap φ = shortComplexLastCokernelMap ψ := by
  apply (cancel_epi (cokernel.π S.g)).mp
  rw [shortComplexLastCokernelMap_fac, shortComplexLastCokernelMap_fac,
    h.comm₃, h₃, zero_add, Preadditive.add_comp, Category.assoc, cokernel.condition, comp_zero, zero_add]

def shortComplexLastCokernelIso (e : ShortComplex.HomotopyEquiv S T)
    (hh : e.homotopyHomInvId.h₃ = 0) (hi : e.homotopyInvHomId.h₃ = 0) :
    cokernel S.g ≅ cokernel T.g where
  hom := shortComplexLastCokernelMap e.hom
  inv := shortComplexLastCokernelMap e.inv
  hom_inv_id := by
    rw [← shortComplexLastCokernelMap_comp,
      shortComplexLastCokernelMap_homotopy e.homotopyHomInvId hh, shortComplexLastCokernelMap_id]
  inv_hom_id := by
    rw [← shortComplexLastCokernelMap_comp,
      shortComplexLastCokernelMap_homotopy e.homotopyInvHomId hi, shortComplexLastCokernelMap_id]

def dualShortComplexLastCokernelIso
    {R : Type u} [CommRing R] {S T : ShortComplex (ModuleCat.{u} R)}
    (e : ShortComplex.HomotopyEquiv S T)
    (hh : e.homotopyHomInvId.h₀ = 0) (hi : e.homotopyInvHomId.h₀ = 0) :
    cokernel (Module.DualFunctor.dualModuleShortComplex S).g ≅ cokernel (Module.DualFunctor.dualModuleShortComplex T).g := by
  apply shortComplexLastCokernelIso (Dual.ShortComplexHomotopy.dualShortComplexHomotopyEquiv e)
  · change (Module.DualFunctor.moduleDualFunctor R).map e.homotopyHomInvId.h₀.op = 0
    rw [hh, op_zero, Functor.map_zero]
  · change (Module.DualFunctor.moduleDualFunctor R).map e.homotopyInvHomId.h₀.op = 0
    rw [hi, op_zero, Functor.map_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ShortComplexLastCokernel
