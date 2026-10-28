import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ParameterRestriction
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Affine Parameter -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.AffineParameter

noncomputable section

/-! An actual flat affine-line parameter acts regularly on every
stalk, and on native reduced-support modules that are flat over the line. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Polynomial

variable (k : Type) [Field k]

theorem toStalk_injective (p : PrimeSpectrum k[X]) :
    Function.Injective (StructureSheaf.toStalk k[X] p) := by
  let : Algebra k[X] ((Spec (.of k[X])).presheaf.stalk p) :=
    (StructureSheaf.toStalk k[X] p).hom.toAlgebra
  let : IsLocalization p.asIdeal.primeCompl ((Spec (.of k[X])).presheaf.stalk p) := by
    change IsLocalization p.asIdeal.primeCompl ((structurePresheafInCommRingCat k[X]).stalk p)
    infer_instance
  exact IsLocalization.injective ((Spec (.of k[X])).presheaf.stalk p)
    p.asIdeal.primeCompl_le_nonZeroDivisors

theorem base_regular (p : PrimeSpectrum k[X]) (a : k) :
    IsSMulRegular (R := (Spec (.of k[X])).presheaf.stalk p)
      ((Spec (.of k[X])).presheaf.stalk p)
      (StructureSheaf.toStalk k[X] p (Polynomial.X - Polynomial.C a)) := by
  have hne : (StructureSheaf.toStalk k[X] p (Polynomial.X - Polynomial.C a) :
      (Spec (.of k[X])).presheaf.stalk p) ≠ 0 :=
    (map_ne_zero_iff _ (toStalk_injective k p)).mpr (Polynomial.X_sub_C_ne_zero a)
  exact fun _ _ h => mul_left_cancel₀ hne h

theorem regular {Z : Scheme} (t : Z ⟶ Spec (.of k[X])) [Flat t] (x : Z) (a : k) :
    IsSMulRegular (Z.presheaf.stalk x) (Affine.ParameterFiber.germ k t x a) := by
  let R := (Spec (.of k[X])).presheaf.stalk (t x)
  let S := Z.presheaf.stalk x
  let : Algebra R S := (t.stalkMap x).hom.toAlgebra
  let : Module.Flat R S := Flat.stalkMap t x
  exact (base_regular k (t x) a).of_flat

theorem nonzero {Z : Scheme} (t : Z ⟶ Spec (.of k[X])) [Flat t] (x : Z) (a : k) :
    Affine.ParameterFiber.germ k t x a ≠ 0 := by
  intro h
  have hr := regular k t x a
  have he : Affine.ParameterFiber.germ k t x a • (0 : Z.presheaf.stalk x) =
      Affine.ParameterFiber.germ k t x a • (1 : Z.presheaf.stalk x) := by simp [h]
  exact zero_ne_one (hr he)

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

theorem support_regular (Z : Scheme) (W : IrreducibleCloseds Z)
    (t : Z ⟶ Spec (.of ℂ[X])) [Flat (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ t)]
    (x : Z) (hx : x ∈ (W : Set Z)) (a : ℂ) :
    IsSMulRegular (CycleClass.Thom.IntersectionGeometry.localSupportModule Z W x hx) (Affine.ParameterFiber.germ ℂ t x a) := by
  have h := regular ℂ (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ t) (CycleClass.Thom.IntersectionGeometry.supportPreimage W x hx) a
  rw [← Affine.ParameterRestriction.support Z W t x hx a] at h
  exact h

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.AffineParameter
