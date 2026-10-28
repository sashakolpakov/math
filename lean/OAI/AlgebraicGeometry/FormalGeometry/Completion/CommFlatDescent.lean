import OAI.AlgebraicGeometry.FormalGeometry.Completion.CommBaseChange
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.AlgCat.Limits
import Mathlib.Algebra.Category.Ring.Limits

/-! # Comm Flat Descent -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.CommFlatDescent.Construction

noncomputable section

/-!
# Completion: faithfully flat descent for commutative algebras

The actual tensor-product functor preserves finite limits under flatness
and reflects isomorphisms under faithful flatness. Beck's theorem then
gives effective descent in the form of its coalgebra comparison equivalence.
-/

open _root_.CategoryTheory Limits TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (R : Type u) [CommRing R]

/-- Forget multiplication while keeping the module over the actual base ring. -/
def commAlgUnderlyingModule : CommAlgCat.{u} R ⥤ ModuleCat.{u} R where
  obj A := ModuleCat.of R A
  map g := ModuleCat.ofHom g.hom.toLinearMap

instance commAlgForget_preservesLimits : PreservesLimits (forget (CommAlgCat.{u} R)) := by
  have : PreservesLimits (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}) := by
    change PreservesLimits ((commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙
      Under.forget (CommRingCat.of R))
    infer_instance
  change PreservesLimits ((forget₂ (CommAlgCat.{u} R) CommRingCat.{u}) ⋙ forget CommRingCat.{u})
  infer_instance

instance commAlgUnderlyingModule_preservesLimits : PreservesLimits (commAlgUnderlyingModule R) := by
  have : PreservesLimits (commAlgUnderlyingModule R ⋙ forget (ModuleCat.{u} R)) :=
    commAlgForget_preservesLimits R
  exact preservesLimits_of_reflects_of_preserves _ (forget (ModuleCat.{u} R))

instance commAlgUnderlyingModule_reflectsIsomorphisms :
    (commAlgUnderlyingModule R).ReflectsIsomorphisms := by
  have : (commAlgUnderlyingModule R ⋙ forget (ModuleCat.{u} R)).ReflectsIsomorphisms :=
    inferInstanceAs (forget (CommAlgCat.{u} R)).ReflectsIsomorphisms
  exact reflectsIsomorphisms_of_comp _ (forget (ModuleCat.{u} R))

instance commAlgUnderlyingModule_reflectsLimits : ReflectsLimits (commAlgUnderlyingModule R) :=
  reflectsLimits_of_reflectsIsomorphisms

variable {R} {S : Type u} [CommRing S] (f : R →+* S)

/-- Algebra base change has the actual module base change as its underlying functor. -/
def commAlgExtendUnderlyingIso :
    CommBaseChange.Construction.commAlgExtend f ⋙ commAlgUnderlyingModule S ≅
      commAlgUnderlyingModule R ⋙ ModuleCat.extendScalars f := by
  letI : Algebra R S := f.toAlgebra
  refine NatIso.ofComponents (fun A => (LinearEquiv.refl S (S ⊗[R] A)).toModuleIso) ?_
  intro A B g
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change S ⊗[R] A at x
  induction x using TensorProduct.inductionOn with
  | tmul s a =>
    change s • (1 ⊗ₜ[R] g a) = s ⊗ₜ[R] g a
    rw [TensorProduct.smul_tmul']
    change (s * 1) ⊗ₜ[R] g a = s ⊗ₜ[R] g a
    rw [mul_one]
  | add x y hx hy =>
    change _ = _ at hx hy ⊢
    simp only [map_add, hx, hy]

/-- Flat base change preserves finite limits of commutative algebras. -/
theorem commAlgExtend_preservesFiniteLimits (hf : f.Flat) : PreservesFiniteLimits (CommBaseChange.Construction.commAlgExtend f) := by
  have : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  have : PreservesFiniteLimits (commAlgUnderlyingModule R) :=
    PreservesLimits.preservesFiniteLimits _
  have : PreservesFiniteLimits (commAlgUnderlyingModule R ⋙ ModuleCat.extendScalars f) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (CommBaseChange.Construction.commAlgExtend f ⋙ commAlgUnderlyingModule S) :=
    preservesFiniteLimits_of_natIso (commAlgExtendUnderlyingIso f).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (commAlgUnderlyingModule S)

/-- Faithfully flat base change detects isomorphisms of commutative algebras. -/
theorem commAlgExtend_reflectsIsomorphisms (hf : f.FaithfullyFlat) :
    (CommBaseChange.Construction.commAlgExtend f).ReflectsIsomorphisms := by
  have : (ModuleCat.extendScalars.{u, u, u} f).ReflectsIsomorphisms :=
    ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat hf
  have : (CommBaseChange.Construction.commAlgExtend f ⋙ commAlgUnderlyingModule S).ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_iso (commAlgExtendUnderlyingIso f).symm
  exact reflectsIsomorphisms_of_comp _ (commAlgUnderlyingModule S)

/-- Effective faithfully flat algebra descent via the actual tensor-product adjunction. -/
@[instance_reducible]
def commAlgComonadic (hf : f.FaithfullyFlat) : ComonadicLeftAdjoint (CommBaseChange.Construction.commAlgExtend f) := by
  have := commAlgExtend_preservesFiniteLimits f hf.flat
  have := commAlgExtend_reflectsIsomorphisms f hf
  convert! Comonad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms
    (CommBaseChange.Construction.commAlgExtendRestrictAdj f)
  · exact ⟨inferInstance⟩
  · exact ⟨inferInstance⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.CommFlatDescent.Construction
