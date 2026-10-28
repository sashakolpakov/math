import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

/-! # Quotient -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient

noncomputable section

/-!
Quotient gradings for arbitrary graded commutative algebras. The direct-sum
decomposition descends through the homogeneous ideal, yielding the actual
graded quotient ring and its homogeneous quotient map.
-/

open DirectSum

universe u v

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜]

def quotientCoordinateMap (I : HomogeneousIdeal (𝒜)) :
    A →ₗ[R] A ⧸ I.toIdeal :=
  (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap

def quotientGrading (I : HomogeneousIdeal (𝒜)) (d : ℕ) :
    Submodule R (A ⧸ I.toIdeal) :=
  (𝒜 d).map (quotientCoordinateMap I)

def quotientDegreeMap (I : HomogeneousIdeal (𝒜)) (d : ℕ) :
    𝒜 d →ₗ[R] quotientGrading I d :=
  ((quotientCoordinateMap I).comp (𝒜 d).subtype).codRestrict
    (quotientGrading I d) (fun f => ⟨f.val, f.property, rfl⟩)

def quotientPreDecompose (I : HomogeneousIdeal (𝒜)) :
    A →ₗ[R] ⨁ d : ℕ, quotientGrading I d :=
  DirectSum.lmap (quotientDegreeMap I) ∘ₗ (DirectSum.decomposeLinearEquiv (𝒜)).toLinearMap

theorem quotientPreDecompose_mem_kernel (I : HomogeneousIdeal (𝒜)) :
    I.toIdeal.restrictScalars R ≤ LinearMap.ker (quotientPreDecompose I) := by
  intro f hf
  apply DFinsupp.ext
  intro d
  apply Subtype.ext
  change Ideal.Quotient.mk I.toIdeal ((DirectSum.decompose (𝒜) f d).val) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact (Ideal.IsHomogeneous.mem_iff (𝒜) I.isHomogeneous).mp hf d

def quotientDecompose (I : HomogeneousIdeal (𝒜)) :
    (A ⧸ I.toIdeal) →ₗ[R] ⨁ d : ℕ, quotientGrading I d where
  toFun := Quotient.lift (quotientPreDecompose I) (by
    intro f g h
    have hfg : f - g ∈ I.toIdeal := (Submodule.quotientRel_def _).mp h
    have hz : quotientPreDecompose I (f - g) = 0 := quotientPreDecompose_mem_kernel I hfg
    rw [map_sub] at hz
    exact sub_eq_zero.mp hz)
  map_add' x y := Quotient.inductionOn₂ x y (fun f g => map_add (quotientPreDecompose I) f g)
  map_smul' r x := Quotient.inductionOn x (fun f => map_smul (quotientPreDecompose I) r f)

theorem quotientDecompose_mk (I : HomogeneousIdeal (𝒜)) (f : A) :
    quotientDecompose I (Ideal.Quotient.mk I.toIdeal f) = quotientPreDecompose I f := rfl

theorem quotientDecompose_mk_homogeneous (I : HomogeneousIdeal (𝒜))
    (d : ℕ) (f : 𝒜 d) :
    quotientDecompose I (quotientCoordinateMap I f.val) =
      DirectSum.lof R ℕ (fun d => quotientGrading I d) d (quotientDegreeMap I d f) := by
  rw [show quotientCoordinateMap I f.val = Ideal.Quotient.mk I.toIdeal f.val from rfl,
    quotientDecompose_mk]
  change DirectSum.lmap (quotientDegreeMap I) (DirectSum.decomposeLinearEquiv (𝒜) f.val) = _
  rw [DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.lmap_lof]

theorem quotientDecompose_left_inverse (I : HomogeneousIdeal (𝒜)) :
    DirectSum.coeLinearMap (quotientGrading I) ∘ₗ quotientDecompose I = LinearMap.id := by
  have h : (DirectSum.coeLinearMap (quotientGrading I) ∘ₗ quotientDecompose I) ∘ₗ
      quotientCoordinateMap I = quotientCoordinateMap I := by
    apply DirectSum.decompose_lhom_ext (𝒜)
    intro d
    apply LinearMap.ext
    intro f
    change DirectSum.coeLinearMap (quotientGrading I)
      (quotientDecompose I (quotientCoordinateMap I f.val)) = quotientCoordinateMap I f.val
    rw [quotientDecompose_mk_homogeneous, DirectSum.coeLinearMap_lof]
    rfl
  apply LinearMap.ext
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun h f

theorem quotientDecompose_right_inverse (I : HomogeneousIdeal (𝒜)) :
    quotientDecompose I ∘ₗ DirectSum.coeLinearMap (quotientGrading I) = LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro d
  apply LinearMap.ext
  intro x
  obtain ⟨f, hf, hfx⟩ := x.property
  have hx : quotientDegreeMap I d ⟨f, hf⟩ = x := Subtype.ext hfx
  rw [← hx]
  change quotientDecompose I
    (DirectSum.coeLinearMap (quotientGrading I)
      (DirectSum.lof R ℕ (fun d => quotientGrading I d) d (quotientDegreeMap I d ⟨f, hf⟩))) = _
  rw [DirectSum.coeLinearMap_lof]
  exact quotientDecompose_mk_homogeneous I d ⟨f, hf⟩

instance quotientDecomposition (I : HomogeneousIdeal (𝒜)) :
    DirectSum.Decomposition (quotientGrading I) :=
  DirectSum.Decomposition.ofLinearMap (quotientGrading I) (quotientDecompose I)
    (quotientDecompose_left_inverse I) (quotientDecompose_right_inverse I)

instance quotientGradedAlgebra (I : HomogeneousIdeal (𝒜)) :
    GradedAlgebra (quotientGrading I) where
  one_mem := ⟨1, SetLike.one_mem_graded 𝒜, map_one (Ideal.Quotient.mk I.toIdeal)⟩
  mul_mem d e x y hx hy := by
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨g, hg, rfl⟩ := hy
    exact ⟨f * g, SetLike.mul_mem_graded hf hg, map_mul (Ideal.Quotient.mk I.toIdeal) f g⟩

def gradedQuotientMap (I : HomogeneousIdeal (𝒜)) :
    𝒜 →+*ᵍ quotientGrading I where
  __ := Ideal.Quotient.mk I.toIdeal
  map_mem hf := ⟨_, hf, rfl⟩

theorem quotientDegreeMap_surjective (I : HomogeneousIdeal (𝒜)) (d : ℕ) :
    Function.Surjective (quotientDegreeMap I d) := by
  intro x
  obtain ⟨f, hf, hfx⟩ := x.property
  exact ⟨⟨f, hf⟩, Subtype.ext hfx⟩

theorem irrelevant_quotient_le_map (I : HomogeneousIdeal (𝒜)) :
    HomogeneousIdeal.irrelevant (quotientGrading I) ≤
      (HomogeneousIdeal.irrelevant (𝒜)).map (gradedQuotientMap I) := by
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro d hd x hx
  obtain ⟨f, hf, rfl⟩ := hx
  exact Ideal.mem_map_of_mem (gradedQuotientMap I)
    (HomogeneousIdeal.mem_irrelevant_of_mem (𝒜) hd hf)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient
