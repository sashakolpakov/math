import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.DerivedBaseChange
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Flat
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Flat Extension -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FlatExtension

noncomputable section

/-! Flat extension of scalars as an exact functor on actual modules,
preserving projective resolutions and commuting with tensor product. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

def baseChange : ModuleCat.{u} R ⥤ ModuleCat.{u} S where
  obj M := ModuleCat.of S (S ⊗[R] M)
  map f := ModuleCat.ofHom (f.hom.baseChange S)
  map_id _ := by
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_comp (A := S) f.hom g.hom

instance : (FlatExtension.baseChange R S).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_add (A := S) f.hom g.hom

instance : (FlatExtension.baseChange R S).PreservesProjectiveObjects where
  projective_obj {M} hM := by
    let : Projective M := hM
    let : Module.Projective R M := inferInstance
    change Projective (ModuleCat.of S (S ⊗[R] M))
    infer_instance

theorem map_exact [Module.Flat R S] (K : ShortComplex (ModuleCat R)) (hK : K.Exact) :
    (K.map (FlatExtension.baseChange R S)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hK ⊢
  exact Module.Flat.lTensor_exact S hK

instance [Module.Flat R S] : (FlatExtension.baseChange R S).PreservesHomology := by
  exact ((Functor.exact_tfae (FlatExtension.baseChange R S)).out 2 3).mp (map_exact R S)

def tensorIso (M : ModuleCat R) :
    FlatExtension.baseChange R S ⋙ tensorLeft ((FlatExtension.baseChange R S).obj M) ≅
      tensorLeft M ⋙ FlatExtension.baseChange R S :=
  NatIso.ofComponents (fun N =>
    (TensorProduct.AlgebraTensorModule.distribBaseChange R S M N).symm.toModuleIso)
    (by
      intro N N' f
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro a b
      induction a using TensorProduct.inductionOn with
      | tmul s m =>
        induction b using TensorProduct.inductionOn with
        | tmul t n => rfl
        | add b c hb hc => simp only [TensorProduct.tmul_add, map_add, hb, hc]
      | add a c ha hc => simp only [TensorProduct.add_tmul, map_add, ha, hc])

def torBaseChangeIso [Module.Flat R S] (M N : ModuleCat R) (n : ℕ) :
    ((Tor (ModuleCat S) n).obj ((FlatExtension.baseChange R S).obj M)).obj ((FlatExtension.baseChange R S).obj N) ≅
      (FlatExtension.baseChange R S).obj (((Tor (ModuleCat R) n).obj M).obj N) :=
  DerivedBaseChange.leftDerivedIso (tensorLeft M) (tensorLeft ((FlatExtension.baseChange R S).obj M))
    (FlatExtension.baseChange R S) (FlatExtension.baseChange R S) (tensorIso R S M) N n

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FlatExtension
