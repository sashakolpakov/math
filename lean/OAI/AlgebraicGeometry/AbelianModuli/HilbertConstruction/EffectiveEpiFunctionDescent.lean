import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # Effective Epi Function Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EffectiveEpiFunctionDescent

noncomputable section

/-! Regular functions descend uniquely along an effective epimorphism of schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

theorem kernelPair_globalFunctions_condition (f : Y ⟶ X) :
    f.appTop ≫ (pullback.fst f f).appTop = f.appTop ≫ (pullback.snd f f).appTop :=
  (Scheme.Hom.comp_appTop _ _).symm.trans
    ((congrArg Scheme.Hom.appTop (pullback.condition (f := f) (g := f))).trans
      (Scheme.Hom.comp_appTop _ _))

def effectiveEpi_globalFunctions_isLimit (f : Y ⟶ X) [EffectiveEpi f] :
    IsLimit (Fork.ofι f.appTop (kernelPair_globalFunctions_condition f)) := by
  let h := (regularEpiOfEffectiveEpi f).isColimit
  have hw : f.op ≫ (pullback.fst f f).op = f.op ≫ (pullback.snd f f).op :=
    congrArg Quiver.Hom.op (pullback.condition (f := f) (g := f))
  let ho := (Cofork.isColimitOfπEquivIsLimitOp f f pullback.condition hw rfl) h
  exact isLimitForkMapOfIsLimit Scheme.Γ hw ho

theorem effectiveEpi_existsUnique_globalFunction (f : Y ⟶ X) [EffectiveEpi f]
    (r : Γ(Y, ⊤)) (hr : (pullback.fst f f).appTop r = (pullback.snd f f).appTop r) :
    ∃! s : Γ(X, ⊤), f.appTop s = r := by
  let h := isLimitForkMapOfIsLimit (forget CommRingCat) (kernelPair_globalFunctions_condition f)
    (effectiveEpi_globalFunctions_isLimit f)
  exact Types.unique_of_type_equalizer _ _ h r hr

theorem effectiveEpi_appTop_injective (f : Y ⟶ X) [EffectiveEpi f] :
    Function.Injective f.appTop := by
  have : Mono (Scheme.Γ.map f.op) := inferInstance
  exact ConcreteCategory.injective_of_mono_of_preservesPullback (Scheme.Γ.map f.op)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EffectiveEpiFunctionDescent
