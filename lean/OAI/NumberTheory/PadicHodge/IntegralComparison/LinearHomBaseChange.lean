import OAI.NumberTheory.PadicHodge.IntegralComparison.OrientedPurityBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrientedPurityTargetFrame

/-! # Linear Hom Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LinearHomBaseChange

noncomputable section

/-! Flat scalar extension for the original linear Yoneda Hom complex,
with literal evaluation normalization in source and target frames. -/

open _root_.CategoryTheory _root_.HomologicalComplex
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

open OAI.NumberTheory.PadicHodge.IntegralComparison.DualBaseChangeNaturality

abbrev homComplex (P : ChainComplex (ModuleCat.{u} R) ℕ) (N : ModuleCat.{u} R) :=
  ((((linearYoneda R (ModuleCat R)).obj N).mapHomologicalComplex
    (ComplexShape.down ℕ).symm).obj P.op)

def frameIso (P : ChainComplex (ModuleCat.{u} R) ℕ) (N : ModuleCat.{u} R)
    (e : N ≅ ModuleCat.of R R) : homComplex R P N ≅ DualComplexHomology.complex R P :=
  (NatIso.mapHomologicalComplex ((linearYoneda R (ModuleCat R)).mapIso e)
    (ComplexShape.down ℕ).symm).app P.op ≪≫ LinearHomDualPurity.complexIso R P

theorem frame_homologyIso (P : ChainComplex (ModuleCat.{u} R) ℕ) (N : ModuleCat.{u} R)
    (e : N ≅ ModuleCat.of R R) (i : ℕ) :
    homologyMapIso (frameIso R P N e) i =
      LinearHomDualPurity.targetHomologyIso R P N e i := by
  apply Iso.ext
  rw [homologyMapIso_hom, OrientedPurityTargetFrame.targetHomologyIso_hom]
  rfl

variable (P : ChainComplex (ModuleCat.{u} R) ℕ) (Q : ChainComplex (ModuleCat.{u} S) ℕ)
  [∀ i, Module.Free R (P.X i)] [∀ i, Module.Finite R (P.X i)]
  (eP : (DualBaseChangeNaturality.tensorComplex R S).obj P ≅ Q)
  (N : ModuleCat.{u} R) (N' : ModuleCat.{u} S)
  (e : N ≅ ModuleCat.of R R) (e' : N' ≅ ModuleCat.of S S)

def complexIso : (DualBaseChangeNaturality.tensorDualComplex R S).obj (homComplex R P N) ≅ homComplex S Q N' :=
  (DualBaseChangeNaturality.tensorDualComplex R S).mapIso (frameIso R P N e) ≪≫
    DualBaseChangeNaturality.iso R S Q eP ≪≫ (frameIso S Q N' e').symm

def component (i : ℕ) : S ⊗[R] (P.X i ⟶ N) →ₗ[S] (Q.X i ⟶ N') :=
  ((complexIso R S P Q eP N N' e e').hom.f i).hom

omit [Module.Flat R S] in
theorem component_evaluation (i : ℕ) (a b : S) (f : P.X i ⟶ N) (x : P.X i) :
    e'.hom ((component R S P Q eP N N' e e' i (a ⊗ₜ[R] f))
      (eP.hom.f i (b ⊗ₜ[R] x))) = a * b * algebraMap R S (e.hom (f x)) := by
  change e'.hom (e'.inv
    (IntegralComparison.Finite.FreeDualBaseChange.equiv R S (P.X i) (a ⊗ₜ[R] (e.hom.hom.comp f.hom))
      (eP.inv.f i (eP.hom.f i (b ⊗ₜ[R] x))))) = _
  have h₁ : ∀ y, e'.hom (e'.inv y) = y :=
    fun y => ConcreteCategory.congr_hom e'.inv_hom_id y
  have h₂ : eP.inv.f i (eP.hom.f i (b ⊗ₜ[R] x)) = b ⊗ₜ[R] x :=
    ConcreteCategory.congr_hom (congrArg (fun k => k.f i) eP.hom_inv_id) _
  rw [h₁, h₂, IntegralComparison.Finite.FreeDualBaseChange.equiv_tmul]
  rfl

def homologyIso (i : ℕ) :
    (DualBaseChangeNaturality.tensorFunctor R S).obj ((homComplex R P N).homology i) ≅ (homComplex S Q N').homology i :=
  (DualBaseChangeNaturality.tensorFunctor R S).mapIso (LinearHomDualPurity.targetHomologyIso R P N e i) ≪≫
    DualBaseChangeNaturality.homologyIso R S Q eP i ≪≫
      (LinearHomDualPurity.targetHomologyIso S Q N' e' i).symm

theorem homologyIso_frame (i : ℕ) (a : S) (x : (homComplex R P N).homology i) :
    (LinearHomDualPurity.targetHomologyIso S Q N' e' i).hom
        ((homologyIso R S P Q eP N N' e e' i).hom (a ⊗ₜ[R] x)) =
      (DualBaseChangeNaturality.homologyIso R S Q eP i).hom
        (a ⊗ₜ[R] (LinearHomDualPurity.targetHomologyIso R P N e i).hom x) := by
  change (LinearHomDualPurity.targetHomologyIso S Q N' e' i).hom
    ((LinearHomDualPurity.targetHomologyIso S Q N' e' i).inv _) = _
  exact ConcreteCategory.congr_hom
    (LinearHomDualPurity.targetHomologyIso S Q N' e' i).inv_hom_id _

theorem homologyIso_canonical (i : ℕ) :
    (((homComplex R P N).sc i).mapHomologyIso (DualBaseChangeNaturality.tensorFunctor R S)).inv ≫
        homologyMap (complexIso R S P Q eP N N' e e').hom i =
      (homologyIso R S P Q eP N N' e e' i).hom := by
  have h := ShortComplex.mapHomologyIso_inv_naturality
    ((shortComplexFunctor (ModuleCat R) (.up ℕ) i).map (frameIso R P N e).hom)
      (DualBaseChangeNaturality.tensorFunctor R S)
  change (DualBaseChangeNaturality.tensorFunctor R S).map (homologyMap (frameIso R P N e).hom i) ≫
      (((DualComplexHomology.complex R P).sc i).mapHomologyIso (DualBaseChangeNaturality.tensorFunctor R S)).inv =
    (((homComplex R P N).sc i).mapHomologyIso (DualBaseChangeNaturality.tensorFunctor R S)).inv ≫
      homologyMap ((DualBaseChangeNaturality.tensorDualComplex R S).map (frameIso R P N e).hom) i at h
  have hR := congrArg Iso.hom (frame_homologyIso R P N e i)
  have hS := congrArg Iso.inv (frame_homologyIso S Q N' e' i)
  change homologyMap (frameIso R P N e).hom i = _ at hR
  change homologyMap (frameIso S Q N' e').inv i = _ at hS
  dsimp only [complexIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    homologyIso, DualBaseChangeNaturality.homologyIso, Functor.mapIso_hom,
    homologyMapIso_hom]
  rw [homologyMap_comp, homologyMap_comp, ← Category.assoc, ← h, hR, hS]
  simp only [Category.assoc]

def compatibleFrame (eN : (DualBaseChangeNaturality.tensorFunctor R S).obj N ≅ N') : N' ≅ ModuleCat.of S S :=
  eN.symm ≪≫ (DualBaseChangeNaturality.tensorFunctor R S).mapIso e ≪≫
    (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso

omit [Module.Flat R S] in
theorem compatibleFrame_tmul (eN : (DualBaseChangeNaturality.tensorFunctor R S).obj N ≅ N') (a : S) (y : N) :
    (compatibleFrame R S N N' e eN).hom (eN.hom (a ⊗ₜ[R] y)) =
      a * algebraMap R S (e.hom y) := by
  change (TensorProduct.AlgebraTensorModule.rid R S S)
    ((e.hom.hom.baseChange S) (eN.inv (eN.hom (a ⊗ₜ[R] y)))) = _
  rw [show eN.inv (eN.hom (a ⊗ₜ[R] y)) = a ⊗ₜ[R] y from
    ConcreteCategory.congr_hom eN.hom_inv_id _, LinearMap.baseChange_tmul]
  simp [Algebra.smul_def, mul_comm]

omit [Module.Flat R S] in
theorem component_evaluation_literal (eN : (DualBaseChangeNaturality.tensorFunctor R S).obj N ≅ N')
    (i : ℕ) (a b : S) (f : P.X i ⟶ N) (x : P.X i) :
    (component R S P Q eP N N' e (compatibleFrame R S N N' e eN) i (a ⊗ₜ[R] f))
        (eP.hom.f i (b ⊗ₜ[R] x)) = eN.hom ((a * b) ⊗ₜ[R] f x) := by
  apply (ModuleCat.mono_iff_injective (compatibleFrame R S N N' e eN).hom).mp inferInstance
  rw [component_evaluation, compatibleFrame_tmul]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LinearHomBaseChange
