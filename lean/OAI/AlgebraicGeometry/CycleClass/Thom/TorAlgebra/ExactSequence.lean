import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Flat
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Exact Sequence -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExactSequence

noncomputable section

/-! The native Tor functor has a long exact sequence in its first argument.
Tensor a projective resolution of the second argument with a short exact
sequence, then transport its homology sequence to the specified Tor functor. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory

namespace Tor

universe u

variable (R : Type u) [CommRing R]

def tensorComplexFunctor (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    ModuleCat R ⥤ ChainComplex (ModuleCat R) ℕ where
  obj M := ((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj K
  map f := (NatTrans.mapHomologicalComplex ((tensoringLeft (ModuleCat R)).map f) _).app K
  map_id M := by simp
  map_comp f g := by simp

instance (K : ChainComplex (ModuleCat.{u} R) ℕ) : (tensorComplexFunctor R K).Additive where
  map_add := by
    intro M N f g
    apply HomologicalComplex.Hom.ext
    funext i
    exact (tensorRight (K.X i)).map_add

theorem tensor_shortExact (N : ModuleCat.{u} R) (P : ProjectiveResolution N)
    (S : ShortComplex (ModuleCat R)) (hS : S.ShortExact) :
    (S.map (tensorComplexFunctor R P.complex)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  let : Module.Projective R (P.complex.X i) := ModuleCat.projective_of_module_projective _
  let : Module.Flat R (P.complex.X i) := inferInstance
  let : (tensorRight (P.complex.X i)).PreservesHomology :=
    ((Functor.exact_tfae (tensorRight (P.complex.X i))).out 2 3).mp
      (Module.Flat.rTensor_shortComplex_exact (P.complex.X i))
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  exact hS.map (tensorRight (P.complex.X i))

def torIso (N : ModuleCat.{u} R) (P : ProjectiveResolution N) (n : ℕ) :
    (Tor (ModuleCat R) n).flip.obj N ≅
      tensorComplexFunctor R P.complex ⋙
        HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n :=
  NatIso.ofComponents (fun M => P.isoLeftDerivedObj (tensorLeft M) n) (by
    intro M M' f
    change (NatTrans.leftDerived ((tensoringLeft (ModuleCat R)).map f) n).app N ≫ _ = _
    rw [P.leftDerived_app_eq]
    simp [tensorComplexFunctor])

instance (N : ModuleCat.{u} R) (n : ℕ) : ((Tor (ModuleCat R) n).flip.obj N).Additive :=
  Functor.additive_of_iso (torIso R N (projectiveResolution N) n).symm

theorem iso_hom_naturality (N : ModuleCat.{u} R) (P : ProjectiveResolution N)
    (n : ℕ) {M M' : ModuleCat R} (f : M ⟶ M') :
    ((Tor (ModuleCat R) n).map f).app N ≫ (P.isoLeftDerivedObj (tensorLeft M') n).hom =
      (P.isoLeftDerivedObj (tensorLeft M) n).hom ≫
        HomologicalComplex.homologyMap ((tensorComplexFunctor R P.complex).map f) n :=
  (torIso R N P n).hom.naturality f

theorem iso_inv_naturality (N : ModuleCat.{u} R) (P : ProjectiveResolution N)
    (n : ℕ) {M M' : ModuleCat R} (f : M ⟶ M') :
    (P.isoLeftDerivedObj (tensorLeft M) n).inv ≫ ((Tor (ModuleCat R) n).map f).app N =
      HomologicalComplex.homologyMap ((tensorComplexFunctor R P.complex).map f) n ≫
        (P.isoLeftDerivedObj (tensorLeft M') n).inv :=
  ((torIso R N P n).inv.naturality f).symm

def connecting (N : ModuleCat.{u} R) (S : ShortComplex (ModuleCat R))
    (hS : S.ShortExact) (n : ℕ) :
    (((Tor (ModuleCat R) (n + 1)).obj S.X₃).obj N) ⟶
      (((Tor (ModuleCat R) n).obj S.X₁).obj N) :=
  ((projectiveResolution N).isoLeftDerivedObj (tensorLeft S.X₃) (n + 1)).hom ≫
    (tensor_shortExact R N (projectiveResolution N) S hS).δ (n + 1) n (by simp) ≫
      ((projectiveResolution N).isoLeftDerivedObj (tensorLeft S.X₁) n).inv

theorem connecting_comp (N : ModuleCat.{u} R) (S : ShortComplex (ModuleCat R))
    (hS : S.ShortExact) (n : ℕ) :
    connecting R N S hS n ≫ ((Tor (ModuleCat R) n).map S.f).app N = 0 := by
  dsimp only [connecting]
  rw [Category.assoc, Category.assoc, iso_inv_naturality]
  have h := (tensor_shortExact R N (projectiveResolution N) S hS).δ_comp (n + 1) n (by simp)
  simpa only [Category.assoc, comp_zero, zero_comp, ShortComplex.map_f] using congrArg
    (fun k => ((projectiveResolution N).isoLeftDerivedObj (tensorLeft S.X₃) (n + 1)).hom ≫
      k ≫ ((projectiveResolution N).isoLeftDerivedObj (tensorLeft S.X₂) n).inv) h

theorem comp_connecting (N : ModuleCat.{u} R) (S : ShortComplex (ModuleCat R))
    (hS : S.ShortExact) (n : ℕ) :
    ((Tor (ModuleCat R) (n + 1)).map S.g).app N ≫ connecting R N S hS n = 0 := by
  dsimp only [connecting]
  rw [← Category.assoc, ← Category.assoc, iso_hom_naturality]
  have h := (tensor_shortExact R N (projectiveResolution N) S hS).comp_δ (n + 1) n (by simp)
  simpa only [Category.assoc, comp_zero, zero_comp, ShortComplex.map_g] using congrArg
    (fun k => ((projectiveResolution N).isoLeftDerivedObj (tensorLeft S.X₂) (n + 1)).hom ≫
      k ≫ ((projectiveResolution N).isoLeftDerivedObj (tensorLeft S.X₁) n).inv) h

theorem exact_middle (N : ModuleCat.{u} R) (S : ShortComplex (ModuleCat R))
    (hS : S.ShortExact) (n : ℕ) :
    (S.map ((Tor (ModuleCat R) n).flip.obj N)).Exact := by
  let P := projectiveResolution N
  have h := (tensor_shortExact R N P S hS).homology_exact₂ n
  apply ShortComplex.exact_of_iso
    (S.mapNatIso (torIso R N P n)).symm
  exact h

theorem epi_zero (N : ModuleCat.{u} R) (S : ShortComplex (ModuleCat R))
    (hS : S.ShortExact) : Epi (((Tor (ModuleCat R) 0).map S.g).app N) := by
  let P := projectiveResolution N
  let T := S.map (tensorComplexFunctor R P.complex)
  have hT := tensor_shortExact R N P S hS
  let : Epi T.g := hT.epi_g
  let : Epi (HomologicalComplex.homologyMap T.g 0) :=
    HomologicalComplex.epi_homologyMap_of_epi_of_not_rel T.g 0 (by simp)
  have h := iso_hom_naturality R N P 0 S.g
  have : Epi ((((Tor (ModuleCat R) 0).map S.g).app N) ≫
      (P.isoLeftDerivedObj (tensorLeft S.X₃) 0).hom) := by
    rw [h]
    exact inferInstanceAs (Epi ((P.isoLeftDerivedObj (tensorLeft S.X₂) 0).hom ≫
      HomologicalComplex.homologyMap T.g 0))
  exact (epi_comp_iff_of_isIso (((Tor (ModuleCat R) 0).map S.g).app N)
    (P.isoLeftDerivedObj (tensorLeft S.X₃) 0).hom).mp inferInstance

theorem exact_after_connecting (N : ModuleCat.{u} R) (S : ShortComplex (ModuleCat R))
    (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk (connecting R N S hS n) (((Tor (ModuleCat R) n).map S.f).app N)
      (connecting_comp R N S hS n)).Exact := by
  let P := projectiveResolution N
  let hT := tensor_shortExact R N P S hS
  let e₁ := (torIso R N P (n + 1)).app S.X₃
  let e₂ := (torIso R N P n).app S.X₁
  let e₃ := (torIso R N P n).app S.X₂
  let e : ShortComplex.mk _ _ (connecting_comp R N S hS n) ≅
      ShortComplex.mk _ _ (hT.δ_comp (n + 1) n (by simp)) :=
    ShortComplex.isoMk e₁ e₂ e₃ (by
      change e₁.hom ≫ hT.δ (n + 1) n (by simp) =
        (e₁.hom ≫ hT.δ (n + 1) n (by simp) ≫ e₂.inv) ≫ e₂.hom
      simp)
      ((torIso R N P n).hom.naturality S.f).symm
  exact ShortComplex.exact_of_iso e.symm (hT.homology_exact₁ (n + 1) n (by simp))

theorem exact_before_connecting (N : ModuleCat.{u} R) (S : ShortComplex (ModuleCat R))
    (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk (((Tor (ModuleCat R) (n + 1)).map S.g).app N)
      (connecting R N S hS n) (comp_connecting R N S hS n)).Exact := by
  let P := projectiveResolution N
  let hT := tensor_shortExact R N P S hS
  let e₁ := (torIso R N P (n + 1)).app S.X₂
  let e₂ := (torIso R N P (n + 1)).app S.X₃
  let e₃ := (torIso R N P n).app S.X₁
  let e : ShortComplex.mk _ _ (comp_connecting R N S hS n) ≅
      ShortComplex.mk _ _ (hT.comp_δ (n + 1) n (by simp)) :=
    ShortComplex.isoMk e₁ e₂ e₃ ((torIso R N P (n + 1)).hom.naturality S.g).symm
      (by
        change e₂.hom ≫ hT.δ (n + 1) n (by simp) =
          (e₂.hom ≫ hT.δ (n + 1) n (by simp) ≫ e₃.inv) ≫ e₃.hom
        simp)
  exact ShortComplex.exact_of_iso e.symm (hT.homology_exact₃ (n + 1) n (by simp))

end Tor

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExactSequence
