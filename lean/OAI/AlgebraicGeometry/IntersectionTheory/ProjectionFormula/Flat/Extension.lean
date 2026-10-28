import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DerivedBaseChange
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Flat
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Extension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.Extension

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

instance : (Extension.baseChange R S).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_add (A := S) f.hom g.hom

instance : (Extension.baseChange R S).PreservesProjectiveObjects where
  projective_obj {M} hM := by
    let : Projective M := hM
    let : Module.Projective R M := inferInstance
    change Projective (ModuleCat.of S (S ⊗[R] M))
    infer_instance

theorem map_exact [Module.Flat R S] (K : ShortComplex (ModuleCat R)) (hK : K.Exact) :
    (K.map (Extension.baseChange R S)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hK ⊢
  exact Module.Flat.lTensor_exact S hK

instance [Module.Flat R S] : (Extension.baseChange R S).PreservesHomology := by
  exact ((Functor.exact_tfae (Extension.baseChange R S)).out 2 3).mp (map_exact R S)

def tensorIso (M : ModuleCat R) :
    Extension.baseChange R S ⋙ tensorLeft ((Extension.baseChange R S).obj M) ≅
      tensorLeft M ⋙ Extension.baseChange R S :=
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
    ((Tor (ModuleCat S) n).obj ((Extension.baseChange R S).obj M)).obj ((Extension.baseChange R S).obj N) ≅
      (Extension.baseChange R S).obj (((Tor (ModuleCat R) n).obj M).obj N) :=
  DerivedBaseChange.leftDerivedIso (tensorLeft M) (tensorLeft ((Extension.baseChange R S).obj M))
    (Extension.baseChange R S) (Extension.baseChange R S) (tensorIso R S M) N n

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.Extension
