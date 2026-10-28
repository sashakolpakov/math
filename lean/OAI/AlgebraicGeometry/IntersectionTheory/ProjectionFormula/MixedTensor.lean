import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.Extension

/-! # Mixed Tensor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MixedTensor

noncomputable section

/-! Tensoring an R-module with an S-module, retaining the S-action.
This exact functor gives one-sided flat base change for native Tor. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (N : ModuleCat.{u} S) [Module R N] [IsScalarTower R S N]

def tensor : ModuleCat.{u} R ⥤ ModuleCat.{u} S where
  obj M := ModuleCat.of S (N ⊗[R] M)
  map f := ModuleCat.ofHom (TensorProduct.AlgebraTensorModule.lTensor S N f.hom)
  map_id _ := by
    apply ModuleCat.hom_ext
    exact TensorProduct.AlgebraTensorModule.map_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro n m
    rfl

instance : (tensor R S N).Additive where
  map_add := by
    intro M M' f g
    apply ModuleCat.hom_ext
    exact (TensorProduct.AlgebraTensorModule.lTensor S N).map_add f.hom g.hom

theorem map_exact [Module.Flat R N] (K : ShortComplex (ModuleCat R)) (hK : K.Exact) :
    (K.map (tensor R S N)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hK ⊢
  exact Module.Flat.lTensor_exact N hK

instance [Module.Flat R N] : (tensor R S N).PreservesHomology :=
  ((Functor.exact_tfae (tensor R S N)).out 2 3).mp (map_exact R S N)

def cancelBaseChange :
    ProjectionFormula.Flat.Extension.baseChange R S ⋙ tensorLeft N ≅ tensor R S N ⋙ 𝟭 _ :=
  NatIso.ofComponents (fun M =>
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N M).toModuleIso)
    (by
      intro M M' f
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro n a
      induction a using TensorProduct.inductionOn with
      | tmul s m => rfl
      | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb])

theorem higherDerived_isZero [Module.Flat R N] (M : ModuleCat.{u} R) (n : ℕ) :
    IsZero (((tensor R S N).leftDerived (n + 1)).obj M) := by
  let P := projectiveResolution M
  apply IsZero.of_iso _ (P.isoLeftDerivedObj (tensor R S N) (n + 1))
  change IsZero ((((tensor R S N).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homology (n + 1))
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  exact (P.exact_succ n).map (tensor R S N)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MixedTensor
