import OAI.NumberTheory.PadicHodge.IntegralComparison.KernelTowerResolution

/-! # Kernel Tower Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KernelTowerMap

noncomputable section

/-! Compatible maps of successive kernel presentations induce maps of
their genuine augmented resolutions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

open OAI.NumberTheory.PadicHodge.IntegralComparison.KernelTowerResolution

structure Hom (T U : KernelTowerResolution.Tower (C := C)) where
  object : ∀ n, T.object n ⟶ U.object n
  term : ∀ n, T.term n ⟶ U.term n
  projection : ∀ n, term n ≫ U.projection n = T.projection n ≫ object n
  inclusion : ∀ n, object (n + 1) ≫ U.inclusion n = T.inclusion n ≫ term n

namespace Hom

variable {T U : KernelTowerResolution.Tower (C := C)} (a : Hom T U)

theorem differential (n : ℕ) :
    a.term (n + 1) ≫ U.differential n = T.differential n ≫ a.term n := by
  simp only [KernelTowerResolution.Tower.differential, ← Category.assoc, a.projection]
  rw [Category.assoc, a.inclusion, ← Category.assoc]

def chainMap : T.complex ⟶ U.complex where
  f := a.term
  comm' i j hij := by
    have h : j + 1 = i := hij
    subst i
    rw [T.complex_d, U.complex_d]
    exact a.differential j

theorem augmentation :
    a.chainMap ≫ U.augmentation = T.augmentation ≫ (ChainComplex.single₀ C).map (a.object 0) := by
  apply HomologicalComplex.to_single_hom_ext
  simpa only [HomologicalComplex.comp_f, Hom.chainMap, KernelTowerResolution.Tower.augmentation_zero,
    ChainComplex.single₀_map_f_zero] using a.projection 0

instance [IsIso (a.object 0)] : QuasiIso a.chainMap := by
  have : QuasiIso (a.chainMap ≫ U.augmentation) := by
    rw [a.augmentation]
    infer_instance
  exact quasiIso_of_comp_right a.chainMap U.augmentation

end Hom

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KernelTowerMap
