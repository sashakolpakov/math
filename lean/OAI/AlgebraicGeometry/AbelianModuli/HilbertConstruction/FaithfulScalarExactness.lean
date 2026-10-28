import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-! # Faithful Scalar Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FaithfulScalarExactness

noncomputable section

/-! Exactness is reflected by native extension along a faithfully flat
ring map, including the canonical isomorphism from affine-scheme sections. -/

open _root_.CategoryTheory

universe u

theorem native_scalar_exact_iff_of_faithfullyFlat
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (hf : f.FaithfullyFlat) (S : ShortComplex (ModuleCat.{u} R)) :
    (S.map (ModuleCat.extendScalars f)).Exact ↔ S.Exact := by
  let : Algebra R A := f.toAlgebra
  have : Module.FaithfullyFlat R A := hf
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact,
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  exact Module.FaithfullyFlat.lTensor_exact_iff_exact R A S.f.hom S.g.hom

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FaithfulScalarExactness
