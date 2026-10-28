import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.AdditiveEvaluation
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Restricted Homology -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.RestrictedHomology.RestrictedHomologyAction

noncomputable section

/-! # The additive homology action of a map into a scalar-restricted complex -/

open _root_.CategoryTheory

universe u v

variable {R : Type u} [CommRing R] (φ : R →+* R)
  (K : CochainComplex (ModuleCat.{v} R) ℕ)

local notation "T" => ModuleCat.restrictScalars φ

def map (f : K ⟶ ((T).mapHomologicalComplex (.up ℕ)).obj K) (n : ℕ) :
    K.homology n →+ K.homology n :=
  Module.AdditiveEvaluation.ModuleAdditiveEvaluation.map (M := K.homology n) (N := (T).obj (K.homology n))
    (HomologicalComplex.homologyMap f n ≫ (Mapped.ComplexHomology.MappedComplexHomology.iso T K n).hom)

theorem apply (f : K ⟶ ((T).mapHomologicalComplex (.up ℕ)).obj K) (n : ℕ) (x : K.homology n) :
    map φ K f n x = (Mapped.ComplexHomology.MappedComplexHomology.iso T K n).hom.hom ((HomologicalComplex.homologyMap f n).hom x) := rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.RestrictedHomology.RestrictedHomologyAction
