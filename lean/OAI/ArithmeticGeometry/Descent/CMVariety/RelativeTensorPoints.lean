import OAI.ArithmeticGeometry.Descent.CMVariety.RegularRelativeCharts
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Relative Tensor Points -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.RelativeTensorPoints.Abelian.RelativeCharts

noncomputable section

/-!
Actual algebra characters of a relative tensor product. Compatible points
on two relative affine schemes give an actual point of their fiber product.
Analytic dependence of every regular function is derived by tensor induction
from analytic dependence on each factor.
-/

open scoped Classical ContDiff TensorProduct

variable {R A B : Type} [CommRing R] [Algebra ℂ R]
  [CommRing A] [Algebra ℂ A] [Algebra R A] [IsScalarTower ℂ R A]
  [CommRing B] [Algebra ℂ B] [Algebra R B] [IsScalarTower ℂ R B]

/-- The actual character on a relative tensor product determined by two
characters agreeing on the base algebra. -/
def relativeTensorPoint (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B)
    (h : x.comp (IsScalarTower.toAlgHom ℂ R A) =
      y.comp (IsScalarTower.toAlgHom ℂ R B)) : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (A ⊗[R] B) := by
  let : Algebra R ℂ := (x.toRingHom.comp (algebraMap R A)).toAlgebra
  let xr : A →ₐ[R] ℂ := { x.toRingHom with commutes' := fun _ => rfl }
  let yr : B →ₐ[R] ℂ := {
    y.toRingHom with
    commutes' := fun r => (DFunLike.congr_fun h r).symm }
  let f := Algebra.TensorProduct.productMap xr yr
  exact {
    f.toRingHom with
    commutes' := fun c => by
      change f (algebraMap ℂ A c ⊗ₜ[R] 1) = algebraMap ℂ ℂ c
      rw [Algebra.TensorProduct.productMap_apply_tmul]
      change x (algebraMap ℂ A c) * y 1 = algebraMap ℂ ℂ c
      rw [x.commutes, map_one, mul_one] }

theorem relativeTensorPoint_tmul (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B)
    (h : x.comp (IsScalarTower.toAlgHom ℂ R A) =
      y.comp (IsScalarTower.toAlgHom ℂ R B)) (a : A) (b : B) :
    relativeTensorPoint x y h (a ⊗ₜ[R] b) = x a * y b := rfl

theorem relativeTensorPoint_left (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B)
    (h : x.comp (IsScalarTower.toAlgHom ℂ R A) =
      y.comp (IsScalarTower.toAlgHom ℂ R B)) :
    (relativeTensorPoint x y h).comp Algebra.TensorProduct.includeLeft = x := by
  ext a
  change relativeTensorPoint x y h (a ⊗ₜ[R] 1) = x a
  rw [relativeTensorPoint_tmul, map_one, mul_one]

theorem relativeTensorPoint_right (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B)
    (h : x.comp (IsScalarTower.toAlgHom ℂ R A) =
      y.comp (IsScalarTower.toAlgHom ℂ R B)) :
    (relativeTensorPoint x y h).comp
      ((Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).restrictScalars ℂ) = y := by
  ext b
  change relativeTensorPoint x y h (1 ⊗ₜ[R] b) = y b
  rw [relativeTensorPoint_tmul, map_one, one_mul]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [Algebra ℂ B] [IsScalarTower ℂ R B] in
/-- Analytic evaluation on the two genuine factors proves analytic
evaluation of every element of their relative tensor product. -/
theorem contDiffOn_tensor_evaluation
    (f : E → AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (A ⊗[R] B)) (U : Set E)
    (hA : ∀ a : A, ContDiffOn ℂ ω (fun z => f z (a ⊗ₜ[R] 1)) U)
    (hB : ∀ b : B, ContDiffOn ℂ ω (fun z => f z (1 ⊗ₜ[R] b)) U) :
    ∀ t : A ⊗[R] B, ContDiffOn ℂ ω (fun z => f z t) U := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    have hmul : ∀ z, f z (a ⊗ₜ[R] b) =
        f z (a ⊗ₜ[R] 1) * f z (1 ⊗ₜ[R] b) := by
      intro z
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    simpa only [hmul] using (hA a).mul (hB b)
  | add a b ha hb => simpa only [map_add] using ha.add hb

/-- Construct an actual relative fiber-product point family on the common
domain. A fixed point supplies an arbitrary extension outside that domain;
the analytic conclusion and the factor formulas are on the domain itself. -/
theorem exists_analytic_relativeTensorFamily
    (x : E → AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (y : E → AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (U : Set E)
    (hxy : ∀ z ∈ U, (x z).comp (IsScalarTower.toAlgHom ℂ R A) =
      (y z).comp (IsScalarTower.toAlgHom ℂ R B))
    (hx : ∀ a : A, ContDiffOn ℂ ω (fun z => x z a) U)
    (hy : ∀ b : B, ContDiffOn ℂ ω (fun z => y z b) U)
    (p₀ : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (A ⊗[R] B)) :
    ∃ f : E → AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (A ⊗[R] B),
      (∀ z ∈ U, ∀ a b, f z (a ⊗ₜ[R] b) = x z a * y z b) ∧
      ∀ t : A ⊗[R] B, ContDiffOn ℂ ω (fun z => f z t) U := by
  let f : E → AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (A ⊗[R] B) := fun z =>
    if hz : z ∈ U then relativeTensorPoint (x z) (y z) (hxy z hz) else p₀
  have heval (z : E) (hz : z ∈ U) (a : A) (b : B) :
      f z (a ⊗ₜ[R] b) = x z a * y z b := by
    simp only [f, dite_eq_left hz, relativeTensorPoint_tmul]
  refine ⟨f, heval, contDiffOn_tensor_evaluation f U ?_ ?_⟩
  · intro a
    apply (hx a).congr
    intro z hz
    simpa only [map_one, mul_one] using heval z hz a 1
  · intro b
    apply (hy b).congr
    intro z hz
    simpa only [map_one, one_mul] using heval z hz 1 b

/-- A principal localization adds only regular fractions, so it preserves
analytic dependence of actual algebra characters. -/
theorem contDiffOn_localized_evaluation (g : A)
    (f : E → AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (Localization.Away g)) (U : Set E)
    (hf : ∀ a : A, ContDiffOn ℂ ω
      (fun z => f z (algebraMap A (Localization.Away g) a)) U) :
    ∀ a : Localization.Away g, ContDiffOn ℂ ω (fun z => f z a) U := by
  intro a
  let ak := IsLocalization.Away.sec g a
  have hnonzero (z : E) : f z (algebraMap A (Localization.Away g) g) ≠ 0 :=
    (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph g (f z)).property
  apply ((hf ak.1).div ((hf g).pow ak.2) (fun z _ =>
    pow_ne_zero ak.2 (hnonzero z))).congr
  intro z _
  exact AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineCharts.localizedPoint_eval_eq_div g (f z) a

/-- Construct a point family on a principal open from the actual original
family. The inverse-localization formulas prove all analytic evaluations. -/
theorem exists_analytic_localizedFamily (g : A)
    (f : E → AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (U : Set E)
    (hf : ∀ a : A, ContDiffOn ℂ ω (fun z => f z a) U)
    (p₀ : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (Localization.Away g)) :
    ∃ fg : E → AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (Localization.Away g),
      (∀ z ∈ U ∩ {z | f z g ≠ 0},
        AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction g (fg z) = f z) ∧
      ∀ a : Localization.Away g, ContDiffOn ℂ ω (fun z => fg z a)
        (U ∩ {z | f z g ≠ 0}) := by
  let V := U ∩ {z | f z g ≠ 0}
  let fg : E → AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (Localization.Away g) := fun z =>
    if hz : z ∈ V then AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint (f z) g hz.2 else p₀
  have hfg (z : E) (hz : z ∈ V) :
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction g (fg z) = f z := by
    simp only [fg, dite_eq_left hz]
    exact AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint_comp (f z) g hz.2
  refine ⟨fg, hfg, contDiffOn_localized_evaluation g fg V ?_⟩
  intro a
  apply ((hf a).mono Set.inter_subset_left).congr
  intro z hz
  exact DFunLike.congr_fun (hfg z hz) a

end

end OAI.ArithmeticGeometry.Descent.CMVariety.RelativeTensorPoints.Abelian.RelativeCharts
