import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.RingHom.Flat

/-! # Flat Scalar Exactness -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatScalarExactness

noncomputable section

/-! Native extension along a flat ring map preserves exactness. -/

open _root_.CategoryTheory

universe u

theorem native_scalar_exact_of_flat
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (hf : f.Flat) (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.Exact) : (S.map (ModuleCat.extendScalars f)).Exact := by
  let : Algebra R A := f.toAlgebra
  have : Module.Flat R A := hf
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact Module.Flat.lTensor_exact A hS

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatScalarExactness
