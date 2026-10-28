import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.Submodule.Pointwise

/-! # Regular Category -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.RegularCategory

open _root_.ModuleCat

/- Adapted to HilbertConstruction-local declarations; omit the deprecated alias. -/

universe u v w

variable {R : Type u} [CommRing R] (M : ModuleCat.{v} R)

open _root_.CategoryTheory Abelian Pointwise

lemma LinearMap.exact_lsmul_mkQ_smul_top (M : Type v) [AddCommGroup M] [Module R M] (r : R) :
    Function.Exact (LinearMap.lsmul _ M r) (r • (⊤ : Submodule R M)).mkQ := by
  intro x
  simp [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_smul_pointwise_iff_exists]

namespace ModuleCat

/-- The short (exact) complex `M → M → M⧸xM` obtain from the scalar multiple of `x: R` on `M`. -/
@[simps!]
def smulShortComplex (r : R) : ShortComplex (ModuleCat R) :=
  ModuleCat.shortComplexOfCompEqZero (LinearMap.lsmul _ M r) (r • (⊤ : Submodule R M)).mkQ
    (RegularCategory.LinearMap.exact_lsmul_mkQ_smul_top M r).linearMap_comp_eq_zero

@[simp]
lemma smulShortComplex_f_eq_smul_id (r : R) : (smulShortComplex M r).f = r • 𝟙 M := rfl

lemma smulShortComplex_exact (r : R) : (smulShortComplex M r).Exact :=
  ModuleCat.shortComplex_exact _ (RegularCategory.LinearMap.exact_lsmul_mkQ_smul_top M r)

instance smulShortComplex_g_epi (r : R) : Epi (smulShortComplex M r).g := by
  simpa [smulShortComplex, ModuleCat.epi_iff_surjective] using Submodule.mkQ_surjective _

end ModuleCat

variable {M} in
lemma IsSMulRegular.smulShortComplex_shortExact {r : R} (reg : IsSMulRegular M r) :
    (RegularCategory.ModuleCat.smulShortComplex M r).ShortExact where
  exact := RegularCategory.ModuleCat.smulShortComplex_exact M r
  mono_f := by simpa [RegularCategory.ModuleCat.smulShortComplex, ModuleCat.mono_iff_injective] using! reg

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.RegularCategory
