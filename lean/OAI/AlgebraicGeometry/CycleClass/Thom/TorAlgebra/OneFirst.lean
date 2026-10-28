import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.DerivedZeroNaturality
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FirstShift
import Mathlib.Algebra.Category.ModuleCat.Kernels

/-! # One First -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.OneFirst

noncomputable section

/-! Native Tor in degree one is the kernel of tensoring the inclusion
in a projective presentation of its first argument. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory

namespace Tor

universe u

variable (R : Type u) [CommRing R]

theorem zero_naturality (N : ModuleCat.{u} R) {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    ((Tor (ModuleCat R) 0).map f).app N ≫ (TorAlgebra.Flat.Tor.torZeroIso R M' N).hom =
      (TorAlgebra.Flat.Tor.torZeroIso R M N).hom ≫ (tensorRight N).map f :=
  DerivedZeroNaturality.naturality ((tensoringLeft (ModuleCat R)).map f) N

variable (N : ModuleCat.{u} R) (S : ShortComplex (ModuleCat R)) (hS : S.ShortExact)
  [Projective S.X₂]

def kernelIso : (((Tor (ModuleCat R) 1).obj S.X₃).obj N) ≅
    ModuleCat.of R ((tensorRight N).map S.f).hom.ker := by
  let : Module.Projective R S.X₂ := ModuleCat.projective_of_module_projective _
  let : Module.Flat R S.X₂ := inferInstance
  let δ := ExactSequence.Tor.connecting R N S hS 0
  let : Mono δ := (ExactSequence.Tor.exact_before_connecting R N S hS 0).mono_g
    ((TorAlgebra.Flat.Tor.higherTor_isZero R S.X₂ N 0).eq_zero_of_src _)
  let e₁ := TorAlgebra.Flat.Tor.torZeroIso R S.X₁ N
  let e₂ := TorAlgebra.Flat.Tor.torZeroIso R S.X₂ N
  let g := (tensorRight N).map S.f
  let : HasKernel g := HasLimit.mk ⟨_, ModuleCat.kernelIsLimit g⟩
  have hw : (δ ≫ e₁.hom) ≫ g = 0 := by
    rw [Category.assoc, ← zero_naturality R N S.f, ← Category.assoc,
      ExactSequence.Tor.connecting_comp, zero_comp]
  let T := ShortComplex.mk (δ ≫ e₁.hom) g hw
  let e : ShortComplex.mk δ (((Tor (ModuleCat R) 0).map S.f).app N)
      (ExactSequence.Tor.connecting_comp R N S hS 0) ≅ T :=
    ShortComplex.isoMk (Iso.refl _) e₁ e₂ (by simp [T]) (zero_naturality R N S.f).symm
  have hT : T.Exact := ShortComplex.exact_of_iso e
    (ExactSequence.Tor.exact_after_connecting R N S hS 0)
  let : Mono T.f := inferInstanceAs (Mono (δ ≫ e₁.hom))
  exact (limit.isoLimitCone ⟨_, hT.fIsKernel⟩).symm ≪≫ ModuleCat.kernelIsoKer g

end Tor

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.OneFirst
