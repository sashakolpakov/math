import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Affine Cokernels -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.AffineCokernels

noncomputable section

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (R : CommRingCat.{u}) {M N : (Spec R).Modules}

def cokernelIso [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    tilde (R := R) (cokernel ((moduleSpecΓFunctor (R := R)).map f)) ≅ cokernel f := by
  let : IsIso ((tilde.adjunction (R := R)).counit.app M) := by
    change IsIso M.fromTildeΓ
    infer_instance
  let : IsIso ((tilde.adjunction (R := R)).counit.app N) := by
    change IsIso N.fromTildeΓ
    infer_instance
  let eM := asIso ((tilde.adjunction (R := R)).counit.app M)
  let eN := asIso ((tilde.adjunction (R := R)).counit.app N)
  refine PreservesCokernel.iso (tilde.functor R) ((moduleSpecΓFunctor (R := R)).map f) ≪≫
    cokernel.mapIso _ _ eM eN ?_
  exact (tilde.adjunction (R := R)).counit.naturality f

theorem quasicoherent [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) : (cokernel f).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (cokernelIso R f) inferInstance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.AffineCokernels
