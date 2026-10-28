import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModuleMaps
import Mathlib.LinearAlgebra.Basis.Defs

/-! # Free Module -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FreeModule

noncomputable section

/-!
# IntegralComparison: a finite relative form basis gives an original-base module isomorphism
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModuleMaps

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  (H Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q)

theorem module_smul (U : C) (n : ℕ) (b : B) (ω : FormData.Forms H Q π U n) :
    @SMul.smul B (ModuleMaps.formsModule H Q π U n) inferInstance b ω =
      @SMul.smul (H.obj U).ring (FormData.Forms H Q π U n) inferInstance ((H.obj U).base b) ω := by
  let : Algebra (Q.obj U).ring (H.obj U).ring := FormData.relativeAlgebra H Q π U
  change @SMul.smul (Q.obj U).ring (FormData.Forms H Q π U n) inferInstance ((Q.obj U).base b) ω =
    @SMul.smul (H.obj U).ring (FormData.Forms H Q π U n) inferInstance ((H.obj U).base b) ω
  have h : algebraMap (Q.obj U).ring (H.obj U).ring ((Q.obj U).base b) = (H.obj U).base b :=
    DFunLike.congr_fun (π.app U).overBase b
  exact (algebraMap_smul (H.obj U).ring ((Q.obj U).base b) (ω : FormData.Forms H Q π U n)).symm.trans
    (congrArg (fun a : (H.obj U).ring => a • (ω : FormData.Forms H Q π U n)) h)

variable (ι : Type) [Fintype ι]

def freeModule (U : C) : ModuleCat.{u} B :=
  (ModuleCat.restrictScalars (H.obj U).base).obj (ModuleCat.of (H.obj U).ring (ι → (H.obj U).ring))

def linearEquiv (U : C) (n : ℕ) (b : Module.Basis ι (H.obj U).ring (FormData.Forms H Q π U n)) :
    freeModule H ι U ≃ₗ[B] ModuleMaps.formsModule H Q π U n :=
  { b.equivFun.symm.toEquiv with
    map_add' := b.equivFun.symm.map_add
    map_smul' := by
      intro a x
      have h := b.equivFun.symm.map_smul ((H.obj U).base a) (x : ι → (H.obj U).ring)
      exact h.trans (module_smul H Q π U n a (b.equivFun.symm (x : ι → (H.obj U).ring))).symm }

theorem linearEquiv_apply (U : C) (n : ℕ) (b : Module.Basis ι (H.obj U).ring (FormData.Forms H Q π U n))
    (x : freeModule H ι U) : linearEquiv H Q π ι U n b x = b.equivFun.symm x := rfl

theorem basis_map {U V : C} (α : U ⟶ V) (n : ℕ)
    (bU : Module.Basis ι (H.obj U).ring (FormData.Forms H Q π U n))
    (bV : Module.Basis ι (H.obj V).ring (FormData.Forms H Q π V n))
    (hb : ∀ i, FormData.formsMap H Q π α n (bV i) = bU i) (x : ι → (H.obj V).ring) :
    FormData.formsMap H Q π α n (bV.equivFun.symm x) = bU.equivFun.symm (fun i => (H.map α).ringMap (x i)) := by
  rw [Module.Basis.equivFun_symm_apply, map_sum, Module.Basis.equivFun_symm_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact (FormMaps.formsMap_smul H Q π α n (x i) (bV i)).trans
    (congrArg (fun ω : FormData.Forms H Q π U n => (H.map α).ringMap (x i) • ω) (hb i))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FreeModule
