import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.FiniteExact

/-! # Cohomology Cokernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CohomologyCokernel.FiniteCohomologyCokernel

noncomputable section

/-! Finite cohomology and a finite following term give a finite cokernel.
This supplies the next finite set of generators in a descending complex reduction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (S : ShortComplex (ModuleCat.{v} R))

theorem finite_opcycles [Module.Finite R S.homology] [Module.Finite R S.X₃] :
    Module.Finite R S.opcycles := by
  let T := ShortComplex.mk S.homologyι S.fromOpcycles S.homologyι_comp_fromOpcycles
  have hT : T.Exact := ShortComplex.exact_of_f_is_kernel _ S.homologyIsKernel
  exact Noetherian.FiniteExact.noetherian_finite_of_exact S.homologyι.hom S.fromOpcycles.hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp hT)

theorem finite_cokernel [Module.Finite R S.homology] [Module.Finite R S.X₃] :
    Module.Finite R (S.X₂ ⧸ S.f.hom.range) := by
  have : Module.Finite R S.opcycles := finite_opcycles S
  exact Module.Finite.equiv S.moduleCatOpcyclesIso.toLinearEquiv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CohomologyCokernel.FiniteCohomologyCokernel
