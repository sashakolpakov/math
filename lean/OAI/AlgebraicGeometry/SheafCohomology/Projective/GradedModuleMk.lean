import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedCyclicSubmodule
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.GradedPolynomialModules

/-! # Graded Module Mk -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedModuleMk.GradedModuleQuotient

noncomputable section

/-! The quotient by a homogeneous submodule carries the actual quotient grading. -/

open DirectSum
universe u v w
variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
variable (P : Submodule A M) (hP : P.IsHomogeneous ℳ)

def quotientMap : M →ₗ[R] M ⧸ P := P.mkQ.restrictScalars R

def grading (d : ℤ) : Submodule R (M ⧸ P) := (ℳ d).map (quotientMap (R := R) P)

def degreeMap (d : ℤ) : ℳ d →ₗ[R] grading ℳ P d :=
  ((quotientMap (R := R) P).comp (ℳ d).subtype).codRestrict (grading ℳ P d)
    (fun x => ⟨x.val, x.property, rfl⟩)

def preDecompose : M →ₗ[R] ⨁ d : ℤ, grading ℳ P d :=
  (DirectSum.lmap (degreeMap ℳ P)).comp (decomposeLinearEquiv ℳ).toLinearMap

include hP in
theorem preDecompose_mem_kernel : P.restrictScalars R ≤ (preDecompose ℳ P).ker := by
  intro x hx
  apply DFinsupp.ext
  intro d
  apply Subtype.ext
  change P.mkQ (decompose ℳ x d).val = 0
  exact (Submodule.Quotient.mk_eq_zero P).mpr (hP d hx)

def quotientDecompose : (M ⧸ P) →ₗ[R] ⨁ d : ℤ, grading ℳ P d where
  toFun := Quotient.lift (preDecompose ℳ P) (by
    intro x y h
    have hxy : x - y ∈ P := (Submodule.quotientRel_def _).mp h
    have hz : preDecompose ℳ P (x - y) = 0 := preDecompose_mem_kernel ℳ P hP hxy
    rw [map_sub] at hz
    exact sub_eq_zero.mp hz)
  map_add' x y := Quotient.inductionOn₂ x y (fun f g => map_add (preDecompose ℳ P) f g)
  map_smul' r x := Quotient.inductionOn x (fun f => map_smul (preDecompose ℳ P) r f)

theorem quotientDecompose_mk (x : M) :
    quotientDecompose ℳ P hP (P.mkQ x) = preDecompose ℳ P x := rfl

theorem quotientDecompose_homogeneous (d : ℤ) (x : ℳ d) :
    quotientDecompose ℳ P hP (quotientMap (R := R) P x.val) =
      DirectSum.lof R ℤ (fun e => grading ℳ P e) d (degreeMap ℳ P d x) := by
  rw [show quotientMap (R := R) P x.val = P.mkQ x.val from rfl, quotientDecompose_mk]
  change DirectSum.lmap (degreeMap ℳ P) (decomposeLinearEquiv ℳ x.val) = _
  rw [decomposeLinearEquiv_apply_coe, DirectSum.lmap_lof]

theorem quotientDecompose_left_inverse :
    (DirectSum.coeLinearMap (grading ℳ P)).comp (quotientDecompose ℳ P hP) = LinearMap.id := by
  have h : ((DirectSum.coeLinearMap (grading ℳ P)).comp (quotientDecompose ℳ P hP)).comp
      (quotientMap (R := R) P) = quotientMap (R := R) P := by
    apply DirectSum.decompose_lhom_ext ℳ
    intro d
    apply LinearMap.ext
    intro x
    change DirectSum.coeLinearMap (grading ℳ P)
      (quotientDecompose ℳ P hP (quotientMap (R := R) P x.val)) = _
    rw [quotientDecompose_homogeneous, DirectSum.coeLinearMap_lof]
    rfl
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := P.mkQ_surjective x
  exact LinearMap.congr_fun h a

theorem quotientDecompose_right_inverse :
    (quotientDecompose ℳ P hP).comp (DirectSum.coeLinearMap (grading ℳ P)) = LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro d
  apply LinearMap.ext
  intro x
  obtain ⟨a, ha, hax⟩ := x.property
  have hx : degreeMap ℳ P d ⟨a, ha⟩ = x := Subtype.ext hax
  rw [← hx]
  change quotientDecompose ℳ P hP (DirectSum.coeLinearMap (grading ℳ P)
    (DirectSum.lof R ℤ (fun e => grading ℳ P e) d (degreeMap ℳ P d ⟨a, ha⟩))) = _
  rw [DirectSum.coeLinearMap_lof]
  exact quotientDecompose_homogeneous ℳ P hP d ⟨a, ha⟩

@[instance_reducible]
def quotientDecomposition : Decomposition (grading ℳ P) :=
  Decomposition.ofLinearMap _ (quotientDecompose ℳ P hP)
    (quotientDecompose_left_inverse ℳ P hP) (quotientDecompose_right_inverse ℳ P hP)

variable (𝒜 : ℤ → Submodule R A) [SetLike.GradedSMul 𝒜 ℳ]

instance quotientGradedSMul : SetLike.GradedSMul 𝒜 (grading ℳ P) where
  smul_mem := by
    intro d e a x ha hx
    obtain ⟨b, hb, rfl⟩ := hx
    refine ⟨a • b, SetLike.GradedSMul.smul_mem ha hb, ?_⟩
    exact P.mkQ.map_smul a b

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedModuleMk.GradedModuleQuotient
