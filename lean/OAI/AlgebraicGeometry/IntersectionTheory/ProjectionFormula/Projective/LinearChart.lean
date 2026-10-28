import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.Data.Matrix.Mul

/-! # Linear Chart -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearChart.Coordinates

/-! Linear changes of homogeneous coordinates as actual graded ring
homomorphisms, with the contravariant composition law. -/

open scoped BigOperators

open _root_.MvPolynomial

def form {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℂ)
    (i : Fin (m + 1)) : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n :=
  ∑ j, C (A i j) * X j

theorem form_homogeneous {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℂ)
    (i : Fin (m + 1)) : IsHomogeneous (form A i) 1 :=
  IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X (A i j) j)

def algebraHom {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℂ) :
    Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m →ₐ[ℂ] Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n := aeval (form A)

@[simp] theorem algebraHom_X {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℂ)
    (i : Fin (m + 1)) : algebraHom A (X i) = form A i := aeval_X _ _

@[simp] theorem algebraHom_C {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℂ)
    (z : ℂ) : algebraHom A (C z) = C z := aeval_C _ _

def gradedHom {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℂ) :
    Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading n where
  __ := (algebraHom A).toRingHom
  map_mem {d} {p} hp := by
    change IsHomogeneous (aeval (form A) p) d
    rw [aeval_def]
    simpa only [one_mul, MvPolynomial.algebraMap_eq] using IsHomogeneous.eval₂ hp
      (C : ℂ →+* Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n) (form A) (isHomogeneous_C _) (form_homogeneous A)

@[simp] theorem gradedHom_apply {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℂ)
    (p : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m) : gradedHom A p = algebraHom A p := rfl

theorem form_one (n : ℕ) (i : Fin (n + 1)) : form (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) i = X i := by
  simp [form, Matrix.one_apply]

theorem algebraHom_one (n : ℕ) : algebraHom (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
    AlgHom.id ℂ (Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [algebraHom_X, form_one, AlgHom.id_apply]

theorem algebraHom_form {l m n : ℕ}
    (A : Matrix (Fin (l + 1)) (Fin (m + 1)) ℂ)
    (B : Matrix (Fin (m + 1)) (Fin (n + 1)) ℂ) (i : Fin (l + 1)) :
    algebraHom B (form A i) = form (A * B) i := by
  simp only [form, map_sum, map_mul, algebraHom_C, algebraHom_X, Matrix.mul_apply]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

theorem algebraHom_mul {l m n : ℕ}
    (A : Matrix (Fin (l + 1)) (Fin (m + 1)) ℂ)
    (B : Matrix (Fin (m + 1)) (Fin (n + 1)) ℂ) :
    algebraHom (A * B) = (algebraHom B).comp (algebraHom A) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [algebraHom_X, AlgHom.comp_apply]
  exact (algebraHom_form A B i).symm

theorem gradedHom_one (n : ℕ) : gradedHom (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
    GradedRingHom.id (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) := by
  apply GradedRingHom.ext
  intro p
  change algebraHom _ p = p
  rw [algebraHom_one, AlgHom.id_apply]

theorem gradedHom_mul {l m n : ℕ}
    (A : Matrix (Fin (l + 1)) (Fin (m + 1)) ℂ)
    (B : Matrix (Fin (m + 1)) (Fin (n + 1)) ℂ) :
    gradedHom (A * B) = (gradedHom B).comp (gradedHom A) := by
  apply GradedRingHom.ext
  intro p
  exact DFunLike.congr_fun (algebraHom_mul A B) p

end AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearChart.Coordinates

namespace AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearChart
section

/-! Invertible linear coordinate changes induce isomorphisms of the
actual projective scheme. These will supply the ambient moving action. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.HomogeneousIdeal

namespace Automorphism

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearChart.Coordinates

theorem irrelevant_le_of_inverse {m n : ℕ}
    (f : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading n)
    (g : Foundations.Scheme.ProjectiveSpace.projectiveGrading n →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading m)
    (hfg : f.comp g = GradedRingHom.id (Foundations.Scheme.ProjectiveSpace.projectiveGrading n)) :
    HomogeneousIdeal.irrelevant (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) ≤
      (HomogeneousIdeal.irrelevant (Foundations.Scheme.ProjectiveSpace.projectiveGrading m)).map f := by
  apply (HomogeneousIdeal.irrelevant_le (Foundations.Scheme.ProjectiveSpace.projectiveGrading n)).mpr
  intro d hd p hp
  have hq : g p ∈ HomogeneousIdeal.irrelevant (Foundations.Scheme.ProjectiveSpace.projectiveGrading m) :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ hd (g.map_mem hp)
  have he : f (g p) = p := DFunLike.congr_fun hfg p
  have hm := Ideal.mem_map_of_mem f.toRingHom hq
  exact he ▸ hm

variable {n : ℕ} (A : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ)

theorem irrelevant_le :
    HomogeneousIdeal.irrelevant (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) ≤
      (HomogeneousIdeal.irrelevant (Foundations.Scheme.ProjectiveSpace.projectiveGrading n)).map (Coordinates.gradedHom A.val) := by
  apply irrelevant_le_of_inverse (Coordinates.gradedHom A.val) (Coordinates.gradedHom A.inv)
  rw [← Coordinates.gradedHom_mul, A.inv_val, Coordinates.gradedHom_one]

def map : Foundations.Scheme.ProjectiveSpace.projectiveSpace n ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n := Proj.map (Coordinates.gradedHom A.val) (Automorphism.irrelevant_le A)

theorem map_one : Automorphism.map (1 : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ) = 𝟙 (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) := by
  unfold Automorphism.map
  simp only [Units.val_one, Coordinates.gradedHom_one, Proj.map_id]

theorem map_mul (B : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ) :
    Automorphism.map (A * B) = Automorphism.map B ≫ Automorphism.map A := by
  unfold Automorphism.map
  simp only [Units.val_mul, Coordinates.gradedHom_mul]
  exact Proj.map_comp (Coordinates.gradedHom A.val) (Coordinates.gradedHom B.val) (Automorphism.irrelevant_le A) (Automorphism.irrelevant_le B)

def iso : Foundations.Scheme.ProjectiveSpace.projectiveSpace n ≅ Foundations.Scheme.ProjectiveSpace.projectiveSpace n where
  hom := Automorphism.map A
  inv := Automorphism.map A⁻¹
  hom_inv_id := by rw [← Automorphism.map_mul, inv_mul_cancel, map_one]
  inv_hom_id := by rw [← Automorphism.map_mul, mul_inv_cancel, map_one]

end Automorphism

end

section

/-! Graded coordinate maps fixing the complex constants commute with
the actual projective structure morphism to Spec ℂ. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace OverBase

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearChart.Coordinates OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearChart.Automorphism

theorem away_constants {m n : ℕ}
    (f : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading n)
    (hC : ∀ z : ℂ, f (MvPolynomial.C z) = MvPolynomial.C z)
    (s : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m) (z : ℂ) :
    HomogeneousLocalization.Away.map f s
      (HomogeneousLocalization.fromZeroRingHom (Foundations.Scheme.ProjectiveSpace.projectiveGrading m) (Submonoid.powers s)
        (Foundations.Scheme.ProjectiveSpace.degreeZeroConstants m z)) =
      HomogeneousLocalization.fromZeroRingHom (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (Submonoid.powers (f s))
        (Foundations.Scheme.ProjectiveSpace.degreeZeroConstants n z) := by
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.fromZeroRingHom, HomogeneousLocalization.Away.map,
    HomogeneousLocalization.map_mk, hC]

theorem graded_over_base {m n : ℕ}
    (f : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading n)
    (hf : HomogeneousIdeal.irrelevant (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) ≤
      (HomogeneousIdeal.irrelevant (Foundations.Scheme.ProjectiveSpace.projectiveGrading m)).map f)
    (hC : ∀ z : ℂ, f (MvPolynomial.C z) = MvPolynomial.C z) :
    Proj.map f hf ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m = Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n := by
  apply (Proj.mapAffineOpenCover f hf).openCover.hom_ext
  intro s
  change Proj.awayι (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f s.2) (f.map_mem s.2.2) s.1.2 ≫
      (Proj.map f hf ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m) =
    Proj.awayι (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f s.2) (f.map_mem s.2.2) s.1.2 ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n
  rw [← Category.assoc, Proj.awayι_comp_map f hf s.1.2 s.2 s.2.2, Category.assoc,
    Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase_chart m, Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase_chart n, ← Spec.map_comp]
  congr 1
  ext z
  exact congrArg HomogeneousLocalization.val (away_constants f hC s.2 z)

theorem over_base {n : ℕ} (A : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ) :
    Automorphism.map A ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n = Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n :=
  graded_over_base (Coordinates.gradedHom A.val) (Automorphism.irrelevant_le A) (fun z => Coordinates.algebraHom_C A.val z)

def overIso {n : ℕ} (A : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ) :
    Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) ≅ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) :=
  Over.isoMk (Automorphism.iso A) (over_base A)

end OverBase

end

section

/-! A graded coordinate homomorphism defines a scheme map on each
homogeneous chart where its selected coordinate does not vanish. No
global irrelevant-ideal condition is imposed on the coordinate map. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization

namespace Hom

variable {m n : ℕ} (f : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading n)

def affine (s : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m) {d : ℕ} (hs : s ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading m d) (hd : 0 < d) :
    Spec (.of (Away (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f s))) ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace m :=
  Spec.map (CommRingCat.ofHom (Away.map f s)) ≫ Proj.awayι (Foundations.Scheme.ProjectiveSpace.projectiveGrading m) s hs hd

def chart (s : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m) {d : ℕ} (hs : s ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading m d) (hd : 0 < d) :
    (Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f s)).toScheme ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace m :=
  (Proj.basicOpenIsoSpec (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f s) (f.map_mem hs) hd).hom ≫ affine f s hs hd

theorem affine_over_base
    (hC : ∀ z : ℂ, f (MvPolynomial.C z) = MvPolynomial.C z)
    (s : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m) {d : ℕ} (hs : s ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading m d) (hd : 0 < d) :
    affine f s hs hd ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m =
      Proj.awayι (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f s) (f.map_mem hs) hd ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n := by
  rw [affine, Category.assoc, Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase_chart m,
    Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase_chart n, ← Spec.map_comp]
  congr 1
  ext z
  exact congrArg HomogeneousLocalization.val (OverBase.away_constants f hC s z)

theorem chart_over_base
    (hC : ∀ z : ℂ, f (MvPolynomial.C z) = MvPolynomial.C z)
    (s : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m) {d : ℕ} (hs : s ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading m d) (hd : 0 < d) :
    chart f s hs hd ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m =
      (Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f s)).ι ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n := by
  rw [chart, Category.assoc, affine_over_base f hC s hs hd, Proj.awayι]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

theorem away_naturality (s t : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m) {d e : ℕ}
    (hs : s ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading m d) (ht : t ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading m e) :
    (awayMap (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f.map_mem ht) (map_mul f s t)).comp (Away.map f s) =
      (Away.map f (s * t)).comp (awayMap (Foundations.Scheme.ProjectiveSpace.projectiveGrading m) ht rfl) := by
  apply RingHom.ext
  intro a
  obtain ⟨r, a, ha, rfl⟩ := Away.mk_surjective (Foundations.Scheme.ProjectiveSpace.projectiveGrading m) hs a
  simp only [RingHom.comp_apply, Away.map_mk, awayMap_mk, map_mul, map_pow]
  rfl

theorem affine_product (s t : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m) {d e : ℕ}
    (hs : s ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading m d) (ht : t ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading m e) (hd : 0 < d) :
    Spec.map (CommRingCat.ofHom (awayMap (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f.map_mem ht) (map_mul f s t))) ≫
        affine f s hs hd =
      affine f (s * t) (SetLike.mul_mem_graded hs ht) (hd.trans_le (Nat.le_add_right d e)) := by
  rw [affine, ← Category.assoc, ← Spec.map_comp]
  have he := congrArg CommRingCat.ofHom (away_naturality f s t hs ht)
  change CommRingCat.ofHom (Away.map f s) ≫
    CommRingCat.ofHom (awayMap (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f.map_mem ht) (map_mul f s t)) =
    CommRingCat.ofHom (awayMap (Foundations.Scheme.ProjectiveSpace.projectiveGrading m) ht rfl) ≫ CommRingCat.ofHom (Away.map f (s * t)) at he
  rw [he, Spec.map_comp, Category.assoc]
  exact congrArg (fun k => Spec.map (CommRingCat.ofHom (Away.map f (s * t))) ≫ k)
    (Proj.SpecMap_awayMap_awayι (𝒜 := Foundations.Scheme.ProjectiveSpace.projectiveGrading m) hs hd ht (x := s * t) rfl)

end Hom

end

/-! The chart maps induced by a graded coordinate homomorphism agree
on all common open subcharts. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization

namespace Overlap

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearChart.Hom

variable {m n : ℕ} (f : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading n)

theorem chart_independent (s : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m) {d e : ℕ}
    (hs : s ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading m d) (ht : s ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading m e) (hd : 0 < d) (he : 0 < e) :
    Hom.chart f s hs hd = Hom.chart f s ht he := rfl

theorem chart_product (s t x : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m) {d e : ℕ}
    (hs : s ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading m d) (ht : t ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading m e) (hd : 0 < d) (hx : x = s * t) :
    (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).homOfLE
        (Proj.basicOpen_mono _ _ _ ⟨f t, (congrArg f hx).trans (map_mul f s t)⟩) ≫
      Hom.chart f s hs hd =
      Hom.chart f x (hx ▸ SetLike.mul_mem_graded hs ht) (hd.trans_le (Nat.le_add_right d e)) := by
  subst x
  rw [Hom.chart, Hom.chart, Proj.basicOpenIsoSpec_hom, Proj.basicOpenIsoSpec_hom, ← Category.assoc,
    ← Proj.basicOpenToSpec_SpecMap_awayMap (𝒜 := Foundations.Scheme.ProjectiveSpace.projectiveGrading n)
      (f.map_mem ht) (map_mul f s t), Category.assoc, Hom.affine_product f s t hs ht hd]

theorem agree (s t : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m) {d e : ℕ}
    (hs : s ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading m d) (ht : t ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading m e) (hd : 0 < d) (he : 0 < e)
    (U : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Opens)
    (hUs : U ≤ Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f s))
    (hUt : U ≤ Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f t)) :
    (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).homOfLE hUs ≫ Hom.chart f s hs hd =
      (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).homOfLE hUt ≫ Hom.chart f t ht he := by
  have hU : U ≤ Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f (s * t)) := by
    rw [map_mul, Proj.basicOpen_mul]
    exact le_inf hUs hUt
  have hleft := chart_product f s t (s * t) hs ht hd rfl
  have hright := chart_product f t s (s * t) ht hs he (mul_comm s t)
  have hc := chart_independent f (s * t) (SetLike.mul_mem_graded hs ht)
    ((mul_comm s t) ▸ SetLike.mul_mem_graded ht hs)
    (hd.trans_le (Nat.le_add_right d e)) (he.trans_le (Nat.le_add_right e d))
  have h := congrArg (fun k => (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).homOfLE hU ≫ k)
    (hleft.trans (hc.trans hright.symm))
  simpa only [← Category.assoc, Scheme.homOfLE_homOfLE] using h

end Overlap

end AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearChart

end

end OAI
