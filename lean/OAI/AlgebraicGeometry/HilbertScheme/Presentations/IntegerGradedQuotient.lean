import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IntegerPolynomialGrading
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Integer Graded Quotient -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.IntegerGradedQuotient.GradedModules.IntegerQuotient

noncomputable section

/-! The actual quotient ring by an integer-homogeneous ideal inherits its grading. -/

open DirectSum

universe u v

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] (I : HomogeneousIdeal 𝒜)

def quotientMap : A →ₗ[R] A ⧸ I.toIdeal := (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap

def grading (d : ℤ) : Submodule R (A ⧸ I.toIdeal) := (𝒜 d).map (quotientMap 𝒜 I)

def degreeMap (d : ℤ) : 𝒜 d →ₗ[R] grading 𝒜 I d :=
  ((quotientMap 𝒜 I).comp (𝒜 d).subtype).codRestrict (grading 𝒜 I d)
    (fun x => ⟨x.val, x.property, rfl⟩)

def preDecompose : A →ₗ[R] ⨁ d : ℤ, grading 𝒜 I d :=
  (DirectSum.lmap (degreeMap 𝒜 I)).comp (decomposeLinearEquiv 𝒜).toLinearMap

theorem preDecompose_mem_kernel : I.toIdeal.restrictScalars R ≤ (preDecompose 𝒜 I).ker := by
  intro x hx
  apply DFinsupp.ext
  intro d
  apply Subtype.ext
  change Ideal.Quotient.mk I.toIdeal (decompose 𝒜 x d).val = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact (Ideal.IsHomogeneous.mem_iff 𝒜 I.isHomogeneous).mp hx d

def quotientDecompose : (A ⧸ I.toIdeal) →ₗ[R] ⨁ d : ℤ, grading 𝒜 I d where
  toFun := Quotient.lift (preDecompose 𝒜 I) (by
    intro x y h
    have hxy : x - y ∈ I.toIdeal := (Submodule.quotientRel_def _).mp h
    have hz : preDecompose 𝒜 I (x - y) = 0 := preDecompose_mem_kernel 𝒜 I hxy
    rw [map_sub] at hz
    exact sub_eq_zero.mp hz)
  map_add' x y := Quotient.inductionOn₂ x y (fun f g => map_add (preDecompose 𝒜 I) f g)
  map_smul' r x := Quotient.inductionOn x (fun f => map_smul (preDecompose 𝒜 I) r f)

theorem quotientDecompose_mk (x : A) :
    quotientDecompose 𝒜 I (Ideal.Quotient.mk I.toIdeal x) = preDecompose 𝒜 I x := rfl

theorem quotientDecompose_homogeneous (d : ℤ) (x : 𝒜 d) :
    quotientDecompose 𝒜 I (quotientMap 𝒜 I x.val) =
      DirectSum.lof R ℤ (fun d => grading 𝒜 I d) d (degreeMap 𝒜 I d x) := by
  rw [show quotientMap 𝒜 I x.val = Ideal.Quotient.mk I.toIdeal x.val from rfl, quotientDecompose_mk]
  change DirectSum.lmap (degreeMap 𝒜 I) (decomposeLinearEquiv 𝒜 x.val) = _
  rw [decomposeLinearEquiv_apply_coe, DirectSum.lmap_lof]

theorem quotientDecompose_left_inverse :
    (DirectSum.coeLinearMap (grading 𝒜 I)).comp (quotientDecompose 𝒜 I) = LinearMap.id := by
  have h : ((DirectSum.coeLinearMap (grading 𝒜 I)).comp (quotientDecompose 𝒜 I)).comp
      (quotientMap 𝒜 I) = quotientMap 𝒜 I := by
    apply DirectSum.decompose_lhom_ext 𝒜
    intro d
    apply LinearMap.ext
    intro x
    change DirectSum.coeLinearMap (grading 𝒜 I) (quotientDecompose 𝒜 I (quotientMap 𝒜 I x.val)) = _
    rw [quotientDecompose_homogeneous, DirectSum.coeLinearMap_lof]
    rfl
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact LinearMap.congr_fun h a

theorem quotientDecompose_right_inverse :
    (quotientDecompose 𝒜 I).comp (DirectSum.coeLinearMap (grading 𝒜 I)) = LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro d
  apply LinearMap.ext
  intro x
  obtain ⟨a, ha, hax⟩ := x.property
  have hx : degreeMap 𝒜 I d ⟨a, ha⟩ = x := Subtype.ext hax
  rw [← hx]
  change quotientDecompose 𝒜 I (DirectSum.coeLinearMap (grading 𝒜 I)
    (DirectSum.lof R ℤ (fun d => grading 𝒜 I d) d (degreeMap 𝒜 I d ⟨a, ha⟩))) = _
  rw [DirectSum.coeLinearMap_lof]
  exact quotientDecompose_homogeneous 𝒜 I d ⟨a, ha⟩

instance quotientDecomposition : Decomposition (grading 𝒜 I) :=
  Decomposition.ofLinearMap _ (quotientDecompose 𝒜 I)
    (quotientDecompose_left_inverse 𝒜 I) (quotientDecompose_right_inverse 𝒜 I)

instance quotientGradedAlgebra : GradedAlgebra (grading 𝒜 I) where
  one_mem := ⟨1, SetLike.GradedOne.one_mem, map_one (Ideal.Quotient.mk I.toIdeal)⟩
  mul_mem d e x y hx hy := by
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a * b, SetLike.mul_mem_graded ha hb, map_mul (Ideal.Quotient.mk I.toIdeal) a b⟩

instance quotientGradedSMul : SetLike.GradedSMul 𝒜 (grading 𝒜 I) where
  smul_mem := by
    intro d e a x ha hx
    obtain ⟨b, hb, rfl⟩ := hx
    refine ⟨a * b, SetLike.mul_mem_graded ha hb, ?_⟩
    change Ideal.Quotient.mk I.toIdeal (a * b) = a • Ideal.Quotient.mk I.toIdeal b
    rw [map_mul]
    rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.IntegerGradedQuotient.GradedModules.IntegerQuotient
