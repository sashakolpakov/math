import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.BoundedResolution
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Flat
import Mathlib.RingTheory.Regular.Category
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # Principal -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Principal

noncomputable section

/-! Native Tor against a quotient by a regular element. If the element
also acts injectively on the first module, every higher Tor vanishes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct Pointwise

namespace Tor

universe u

variable (R : Type u) [CommRing R] (r : R)

def resolution (hr : IsSMulRegular R r) :
    ProjectiveResolution (ModuleCat.of R (QuotSMulTop r R)) := by
  let : Projective ((ModuleCat.of R R).smulShortComplex r).X₂ :=
    inferInstanceAs (Projective (ModuleCat.of R R))
  exact ResolutionAugment.resolution ((ModuleCat.of R R).smulShortComplex r)
    (IsSMulRegular.smulShortComplex_shortExact hr) (ProjectiveResolution.self (ModuleCat.of R R))

theorem resolution_isZero (hr : IsSMulRegular R r) (n : ℕ) :
    IsZero ((resolution R r hr).complex.X (n + 2)) := by
  change IsZero (((ChainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R R)).X (n + 1))
  exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)

theorem higherTor_isZero (hr : IsSMulRegular R r) (M : ModuleCat.{u} R)
    (hm : IsSMulRegular M r) (n : ℕ) :
    IsZero (((Tor (ModuleCat R) (n + 1)).obj M).obj
      (ModuleCat.of R (QuotSMulTop r R))) := by
  let P := resolution R r hr
  let K := ((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  apply IsZero.of_iso _ (P.isoLeftDerivedObj (tensorLeft M) (n + 1))
  change IsZero (K.homology (n + 1))
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  cases n with
  | zero =>
    rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
    have hz : IsZero (K.X 2) := (tensorLeft M).map_isZero (resolution_isZero R r hr 0)
    apply ((K.sc' 2 1 0).exact_iff_mono (hz.eq_zero_of_src _)).mpr
    change Mono ((tensorLeft M).map (𝟙 (ModuleCat.of R R) ≫ (r • 𝟙 (ModuleCat.of R R))))
    rw [Category.id_comp, Functor.map_smul, CategoryTheory.Functor.map_id]
    rw [ModuleCat.mono_iff_injective]
    exact ((TensorProduct.rid R M).isSMulRegular_congr r).mpr hm
  | succ n =>
    exact HomologicalComplex.ExactAt.of_isZero
      ((tensorLeft M).map_isZero (resolution_isZero R r hr n))

theorem higherTor_length (hr : IsSMulRegular R r) (M : ModuleCat.{u} R)
    (hm : IsSMulRegular M r) (n : ℕ) :
    Module.length R (((Tor (ModuleCat R) (n + 1)).obj M).obj
      (ModuleCat.of R (QuotSMulTop r R))) = 0 := by
  let := ModuleCat.subsingleton_of_isZero (higherTor_isZero R r hr M hm n)
  exact Module.length_eq_zero

theorem euler_length (hr : IsSMulRegular R r) (M : ModuleCat.{u} R)
    (hm : IsSMulRegular M r) (d : ℕ) :
    (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
      (Module.length R (((Tor (ModuleCat R) i).obj M).obj
        (ModuleCat.of R (QuotSMulTop r R)))).toNat) =
      (Module.length R (QuotSMulTop r M)).toNat := by
  have hI : (r • (⊤ : Submodule R R) : Ideal R) = Ideal.span {r} := by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  have hlen : Module.length R (M ⊗[R] (QuotSMulTop r R)) =
      Module.length R (QuotSMulTop r M) := by
    change Module.length R (M ⊗[R] (R ⧸ (r • (⊤ : Submodule R R)))) = _
    rw [hI, (TensorProduct.tensorQuotEquivQuotSMul M (Ideal.span {r})).length_eq,
      Submodule.ideal_span_singleton_smul]
  rw [Finset.sum_range_succ']
  simp [higherTor_length R r hr M hm, Flat.Tor.torZero_length, hlen]

end Tor

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Principal
