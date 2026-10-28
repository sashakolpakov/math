import OAI.AlgebraicGeometry.Crystalline.Cohomology.ScalarExtensionOn
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.HomologyRestriction

/-! # Base Change Homology -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.BaseChangeHomology.SemilinearBaseChangeHomology

noncomputable section

/-! # Flat scalar extension commutes with the original semilinear homology operator -/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (e : R ≃+* R) (t : S ≃+* S)
  (h : ∀ r, t (algebraMap R S r) = algebraMap R S (e r))
  (C : CochainComplex (ModuleCat.{u} R) ℕ)

local notation "P" => OAI.AlgebraicGeometry.Crystalline.Cohomology.IntrinsicScalarExtension.functor R S
def map (f : NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.Map e.toRingHom C C) : NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.Map t.toRingHom
    (((P).mapHomologicalComplex (.up ℕ)).obj C) (((P).mapHomologicalComplex (.up ℕ)).obj C) where
  f j := NumberTheory.PadicHodge.PeriodInvariants.SemilinearBaseChange.baseChange e.toRingHom t.toRingHom h (f.f j)
  comm i j z := by
    change NumberTheory.PadicHodge.PeriodInvariants.SemilinearBaseChange.baseChange e.toRingHom t.toRingHom h (f.f j)
        ((C.d i j).hom.baseChange S z) =
      (C.d i j).hom.baseChange S
        (NumberTheory.PadicHodge.PeriodInvariants.SemilinearBaseChange.baseChange e.toRingHom t.toRingHom h (f.f i) z)
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s x => exact congrArg (fun y => t s ⊗ₜ[R] y) (f.comm i j x)

theorem linearMap_eq (f : NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.Map e.toRingHom C C) :
    NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.linearMap (map R S e t h C f) =
      ScalarExtensionOn.ScalarExtensionTwistedHomology.map R S e t h C
        (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.linearMap f) := by
  apply HomologicalComplex.Hom.ext
  funext j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  let a := ((NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.linearMap (map R S e t h C f)).f j).hom
  let b := ((ScalarExtensionOn.ScalarExtensionTwistedHomology.map R S e t h C
    (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.linearMap f)).f j).hom
  intro z
  change a z = b z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    exact (a.map_add x y).trans ((congrArg₂ (fun c d => c + d) hx hy).trans (b.map_add x y).symm)
  | tmul s x =>
    exact (ScalarExtensionOn.ScalarExtensionTwistedHomology.component R S e t h C
      (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.linearMap f) j s x).symm

variable [Module.Flat R S]

theorem on_tensor (f : NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.Map e.toRingHom C C) (n : ℕ) (s : S) (x : C.homology n) :
    (Mapped.ComplexHomology.MappedComplexHomology.iso P C n).hom
      (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.homologyMap (map R S e t h C f) n
        ((Mapped.ComplexHomology.MappedComplexHomology.iso P C n).inv (s ⊗ₜ[R] x))) =
      t s ⊗ₜ[R] (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.homologyMap f n x) := by
  have ha := ScalarExtensionOn.ScalarExtensionTwistedHomology.on_tensor R S e t h C
    (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.linearMap f) n s x
  rw [← linearMap_eq R S e t h C f] at ha
  have hl := congrArg (Mapped.ComplexHomology.MappedComplexHomology.iso P C n).hom
    (HomologyRestriction.SemilinearHomologyRestriction.original (map R S e t h C f) n
      ((Mapped.ComplexHomology.MappedComplexHomology.iso P C n).inv (s ⊗ₜ[R] x)))
  have hr := congrArg (ScalarExtensionBase.ScalarExtensionTwist.tensor R S (C.homology n) (t s))
    (HomologyRestriction.SemilinearHomologyRestriction.original f n x)
  exact hl.symm.trans (ha.trans hr)

theorem conjugation (f : NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.Map e.toRingHom C C) (n : ℕ) (z : S ⊗[R] C.homology n) :
    (Mapped.ComplexHomology.MappedComplexHomology.iso P C n).hom
      (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.homologyMap (map R S e t h C f) n
        ((Mapped.ComplexHomology.MappedComplexHomology.iso P C n).inv z)) =
      NumberTheory.PadicHodge.PeriodInvariants.SemilinearBaseChange.baseChange e.toRingHom t.toRingHom h (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.homologyMap f n) z := by
  let c := Mapped.ComplexHomology.MappedComplexHomology.iso P C n
  let a : (S ⊗[R] C.homology n) →ₛₗ[t.toRingHom] S ⊗[R] C.homology n :=
    c.hom.hom.comp ((NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.homologyMap (map R S e t h C f) n).comp c.inv.hom)
  let b := NumberTheory.PadicHodge.PeriodInvariants.SemilinearBaseChange.baseChange e.toRingHom t.toRingHom h (NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.homologyMap f n)
  change a z = b z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    exact (a.map_add x y).trans ((congrArg₂ (fun c d => c + d) hx hy).trans (b.map_add x y).symm)
  | tmul s x => exact on_tensor R S e t h C f n s x

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.BaseChangeHomology.SemilinearBaseChangeHomology
