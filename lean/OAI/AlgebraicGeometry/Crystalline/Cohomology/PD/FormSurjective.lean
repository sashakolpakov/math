import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms

/-! # Form Surjective -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormSurjective.PDFormSurjective

noncomputable section

/-!
# Surjectivity of divided-power forms under quotient maps

Every differential form is a finite sum of symbols. Lifting its coefficient
and each entry proves that a surjective PD algebra map induces surjections
on all form modules.
-/

open _root_.CategoryTheory

universe u

variable {R : Type u} [CommRing R] {A B : CommAlgCat.{u} R}
  {I : Ideal A} {J : Ideal B} {δ : DividedPowers I} {ε : DividedPowers J}
  (f : A ⟶ B) (hf : DividedPowers.IsDPMorphism δ ε f.hom.toRingHom)

theorem formMap_D (a : A) :
    DeRhamGlobal.PDDeRhamGlobal.formMap f hf 1 (OneForms.PDOneForms.D R A I δ a) =
      OneForms.PDOneForms.D R B J ε (f a) := by
  rw [OneForms.PDOneForms.D_apply, OneForms.PDOneForms.D_apply]
  have hs := DeRhamGlobal.PDDeRhamGlobal.formMap_symbol f hf 1 1 (fun _ => a)
  simp only [map_one] at hs
  exact hs

include hf in
theorem surjective (hs : Function.Surjective f) (n : ℕ) :
    Function.Surjective (DeRhamGlobal.PDDeRhamGlobal.formMap f hf n) := by
  intro ω
  obtain ⟨ω, rfl⟩ := Submodule.mkQ_surjective (DeRham.PDDeRham.relations R B J ε n) ω
  obtain ⟨ω, rfl⟩ := Submodule.mkQ_surjective (DeRhamPresentationTo.DeRhamPresentation.relations R B n) ω
  induction ω using Finsupp.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy =>
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    exact ⟨x' + y', by simp only [map_add, hx', hy']⟩
  | single v a =>
    obtain ⟨a, rfl⟩ := hs a
    choose w hw using fun i => hs (v i)
    refine ⟨DeRham.PDDeRham.symbol R A I δ a w, ?_⟩
    change DeRhamGlobal.PDDeRhamGlobal.formMap f hf n (DeRham.PDDeRham.symbol R A I δ a w) =
      DeRham.PDDeRham.symbol R B J ε (f a) v
    rw [DeRhamGlobal.PDDeRhamGlobal.formMap_symbol]
    exact congrArg (DeRham.PDDeRham.symbol R B J ε (f a)) (funext hw)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormSurjective.PDFormSurjective
