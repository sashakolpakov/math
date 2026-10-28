import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.Tor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Homology
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Euler

/-! # Tor Kernel -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.TorKernel

noncomputable section

/-! Tor in degree one against a regular principal quotient is the
actual submodule annihilated by the parameter. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct Pointwise

universe u

variable (R : Type u) [CommRing R] (r : R)

def kernelEquiv {M N : ModuleCat.{u} R} (e : M ≃ₗ[R] N) :
    LinearMap.ker (LinearMap.lsmul R M r) ≃ₗ[R]
      LinearMap.ker (LinearMap.lsmul R N r) where
  toFun x := ⟨e x, by
    change r • e x.val = 0
    rw [← e.map_smul]
    exact (congrArg e x.property).trans e.map_zero⟩
  invFun x := ⟨e.symm x, by
    change r • e.symm x.val = 0
    rw [← e.symm.map_smul]
    exact (congrArg e.symm x.property).trans e.symm.map_zero⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_add' x y := Subtype.ext (e.map_add x y)
  map_smul' a x := Subtype.ext (e.map_smul a x)

def homologyOneIso (K : ChainComplex (ModuleCat.{u} R) ℕ) (h₂ : IsZero (K.X 2)) :
    K.homology 1 ≅ ModuleCat.of R (LinearMap.ker (K.d 1 0).hom) :=
  K.homologyIsoSc' 2 1 0 (by simp) (by simp) ≪≫
    (ShortComplex.RightHomologyData.ofHasKernel (K.sc' 2 1 0)
      (h₂.eq_zero_of_src _)).homologyIso ≪≫ ModuleCat.kernelIsoKer (K.d 1 0)

def torOneIso (hr : IsSMulRegular R r) (M : ModuleCat.{u} R) :
    (((Tor (ModuleCat R) 1).obj M).obj (.of R (QuotSMulTop r R))) ≅
      ModuleCat.of R (LinearMap.ker (LinearMap.lsmul R M r)) := by
  let P := Principal.Tor.resolution R r hr
  let K := ((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let e := homologyOneIso R K
    ((tensorLeft M).map_isZero (Principal.Tor.resolution_isZero R r hr 0))
  refine P.isoLeftDerivedObj (tensorLeft M) 1 ≪≫ e ≪≫ ?_
  change ModuleCat.of R (LinearMap.ker
    ((tensorLeft M).map (𝟙 (ModuleCat.of R R) ≫ (r • 𝟙 (ModuleCat.of R R)))).hom) ≅ _
  rw [Category.id_comp, Functor.map_smul, CategoryTheory.Functor.map_id,
    Homology.scalar_hom]
  exact (kernelEquiv R r (TensorProduct.rid R M)).toModuleIso

theorem euler (hr : IsSMulRegular R r) (M : ModuleCat.{u} R) :
    ProjectionFormula.Tor.Euler.euler R M (.of R (QuotSMulTop r R)) 1 =
      ((Module.length R (QuotSMulTop r M)).toNat : ℚ) -
        (Module.length R (LinearMap.ker (LinearMap.lsmul R M r))).toNat := by
  have hI : (r • (⊤ : Submodule R R) : Ideal R) = Ideal.span {r} := by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  have hlen : Module.length R (M ⊗[R] (QuotSMulTop r R)) =
      Module.length R (QuotSMulTop r M) := by
    change Module.length R (M ⊗[R] (R ⧸ (r • (⊤ : Submodule R R)))) = _
    rw [hI, (TensorProduct.tensorQuotEquivQuotSMul M (Ideal.span {r})).length_eq,
      Submodule.ideal_span_singleton_smul]
  simp only [ProjectionFormula.Tor.Euler.euler, Finset.sum_range_succ, Finset.sum_range_zero,
    ExactLength.rationalLength, ProjectionFormula.Tor.Flat.torZero_length,
    (torOneIso R r hr M).toLinearEquiv.length_eq, hlen]
  norm_num
  ring

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.TorKernel
