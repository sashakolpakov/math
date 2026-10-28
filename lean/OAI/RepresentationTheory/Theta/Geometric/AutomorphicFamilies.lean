import OAI.RepresentationTheory.Theta.Geometric.AutomorphySections
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion

/-! # Automorphic Families -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta

/-! Finite families for powers of an arbitrary actual period automorphy factor.
The section and separation constructions specialize the RiemannProjectivity arguments. -/

open OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction

variable {Φ : Torus.Data.CM.ProjectivePeriodData}

structure Section (J : Φ.AutomorphyFactor) (n : ℕ) where
  toFun : Φ.space → ℂ
  regular : ContDiff ℂ 1 toFun
  translates : ∀ (l : Φ.periodIntegerLattice) (z : Φ.space),
    toFun (z + l.val) = J.value l z ^ n * toFun z

namespace Section

variable {J : Φ.AutomorphyFactor} {n m : ℕ}

instance : CoeFun (Section J n) (fun _ => Φ.space → ℂ) := ⟨toFun⟩

theorem differentiable (s : Section J n) : Differentiable ℂ s :=
  s.regular.differentiable (by norm_num)

theorem continuous (s : Section J n) : Continuous s := s.regular.continuous

theorem continuous_fderiv (s : Section J n) : Continuous (fderiv ℂ s) :=
  s.regular.continuous_fderiv (by norm_num)

def one : Section J 0 where
  toFun _ := 1
  regular := contDiff_const
  translates _ _ := by simp

def mul (s : Section J n) (t : Section J m) : Section J (n + m) where
  toFun z := s z * t z
  regular := s.regular.mul t.regular
  translates l z := by rw [s.translates, t.translates, pow_add]; ring

@[simp]
theorem mul_apply (s : Section J n) (t : Section J m) (z : Φ.space) :
    s.mul t z = s z * t z := rfl

def pow (s : Section J n) (k : ℕ) : Section J (n * k) where
  toFun z := s z ^ k
  regular := s.regular.pow k
  translates l z := by rw [s.translates, mul_pow, pow_mul]

@[simp]
theorem pow_apply (s : Section J n) (k : ℕ) (z : Φ.space) : s.pow k z = s z ^ k := rfl

/-- One of the mixed cubic monomials, in the same degree as `s³`. -/
def squareMul (s t : Section J n) : Section J (n * 3) where
  toFun z := s z ^ 2 * t z
  regular := (s.regular.pow 2).mul t.regular
  translates l z := by
    rw [s.translates, t.translates]
    simp only [mul_pow, pow_mul]
    ring

@[simp]
theorem squareMul_apply (s t : Section J n) (z : Φ.space) : s.squareMul t z = s z ^ 2 * t z := rfl

def add (s t : Section J n) : Section J n where
  toFun z := s z + t z
  regular := s.regular.add t.regular
  translates l z := by rw [s.translates, t.translates, mul_add]

def constMul (c : ℂ) (s : Section J n) : Section J n where
  toFun z := c * s z
  regular := contDiff_const.mul s.regular
  translates l z := by rw [s.translates]; ring

end Section

structure Family (J : Φ.AutomorphyFactor) where
  degree : ℕ
  sections : Finset (Section J degree)
  nonzero : ∀ p : Φ.space, ∃ s ∈ sections, s p ≠ 0

namespace Family

variable {J : Φ.AutomorphyFactor}

def trivial : Family J where
  degree := 0
  sections := {Section.one}
  nonzero _ := ⟨Section.one, Finset.mem_singleton_self _, one_ne_zero⟩

/-- Products of homogeneous coordinates combine two families into one. -/
noncomputable def mul (F G : Family J) : Family J := by
  classical
  exact
    { degree := F.degree + G.degree
      sections := (F.sections ×ˢ G.sections).image (fun st => st.1.mul st.2)
      nonzero := fun p => by
        obtain ⟨s, hs, hsp⟩ := F.nonzero p
        obtain ⟨t, ht, htp⟩ := G.nonzero p
        exact ⟨s.mul t, Finset.mem_image.mpr ⟨(s, t), Finset.mem_product.mpr ⟨hs, ht⟩, rfl⟩,
          mul_ne_zero hsp htp⟩ }

theorem mul_mem (F G : Family J) (s : Section J F.degree)
    (hs : s ∈ F.sections) (t : Section J G.degree) (ht : t ∈ G.sections) :
    s.mul t ∈ (F.mul G).sections := by
  classical
  exact Finset.mem_image.mpr ⟨(s, t), Finset.mem_product.mpr ⟨hs, ht⟩, rfl⟩

def Separates (F : Family J) (p q : Φ.space) : Prop :=
  ∃ s ∈ F.sections, ∃ t ∈ F.sections, s p * t q ≠ s q * t p

def Detects (F : Family J) (p v : Φ.space) : Prop :=
  ∃ s ∈ F.sections, ∃ t ∈ F.sections, s p ≠ 0 ∧
    s p * fderiv ℂ t p v ≠ t p * fderiv ℂ s p v

theorem detects_mul_left (F G : Family J) (p v : Φ.space) (hF : F.Detects p v) :
    (F.mul G).Detects p v := by
  obtain ⟨s, hs, t, ht, hsp, hdet⟩ := hF
  obtain ⟨g, hg, hgp⟩ := G.nonzero p
  refine ⟨s.mul g, mul_mem F G s hs g hg, t.mul g, mul_mem F G t ht g hg,
    mul_ne_zero hsp hgp, ?_⟩
  apply sub_ne_zero.mp
  change Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.wronskian ((s : Φ.space → ℂ) * (g : Φ.space → ℂ)) ((t : Φ.space → ℂ) * (g : Φ.space → ℂ)) p v ≠ 0
  rw [Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.wronskian_mul_right _ _ _ _ _ (s.differentiable p) (t.differentiable p) (g.differentiable p)]
  exact mul_ne_zero (pow_ne_zero 2 hgp) (sub_ne_zero.mpr hdet)

theorem separates_mul_left (F G : Family J) (p q : Φ.space) (hF : F.Separates p q) :
    (F.mul G).Separates p q := by
  obtain ⟨s, hs, t, ht, hdet⟩ := hF
  obtain ⟨g, hg, hgp⟩ := G.nonzero p
  by_cases hgq : g q = 0
  · obtain ⟨h, hh, hhq⟩ := G.nonzero q
    obtain ⟨a, ha, hap⟩ := F.nonzero p
    obtain ⟨b, hb, hbq⟩ := F.nonzero q
    refine ⟨a.mul g, mul_mem F G a ha g hg, b.mul h, mul_mem F G b hb h hh, ?_⟩
    simp only [Section.mul_apply, hgq, mul_zero, zero_mul]
    exact mul_ne_zero (mul_ne_zero hap hgp) (mul_ne_zero hbq hhq)
  · refine ⟨s.mul g, mul_mem F G s hs g hg, t.mul g, mul_mem F G t ht g hg, ?_⟩
    apply sub_ne_zero.mp
    have he : (s.mul g p * t.mul g q) - (s.mul g q * t.mul g p) =
        (g p * g q) * (s p * t q - s q * t p) := by simp only [Section.mul_apply]; ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero hgp hgq) (sub_ne_zero.mpr hdet)

end Family

end RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta

namespace RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family

/-! Projective maps of actual automorphic sections, retaining every coordinate. -/

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates
open Filter _root_.Topology

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}

theorem sections_nonempty (F : Family J) : F.sections.Nonempty := by
  obtain ⟨s, hs, _⟩ := F.nonzero 0
  exact ⟨s, hs⟩

def projectiveDimension (F : Family J) : ℕ := F.sections.card - 1

noncomputable def indexEquiv (F : Family J) :
    F.sections ≃ Fin (F.projectiveDimension + 1) := by
  classical
  apply Finset.equivFinOfCardEq
  have h := Finset.card_pos.mpr F.sections_nonempty
  dsimp [Family.projectiveDimension]
  omega

def coordinate (F : Family J) (i : Fin (F.projectiveDimension + 1)) :
    Section J F.degree := (F.indexEquiv.symm i).val

theorem coordinate_surjective (F : Family J)
    (s : Section J F.degree) (hs : s ∈ F.sections) : ∃ i, F.coordinate i = s := by
  refine ⟨F.indexEquiv ⟨s, hs⟩, ?_⟩
  simp [Family.coordinate]

def vector (F : Family J) (p : Φ.space) : Fin (F.projectiveDimension + 1) → ℂ :=
  fun i => F.coordinate i p

theorem vector_ne_zero (F : Family J) (p : Φ.space) : F.vector p ≠ 0 := by
  obtain ⟨s, hs, hsp⟩ := F.nonzero p
  obtain ⟨i, hi⟩ := F.coordinate_surjective s hs
  intro he
  have hz := congrFun he i
  change F.coordinate i p = 0 at hz
  rw [hi] at hz
  exact hsp hz

def projectiveLift (F : Family J) (p : Φ.space) :
    Projectivization ℂ (Fin (F.projectiveDimension + 1) → ℂ) :=
  Projectivization.mk ℂ (F.vector p) (F.vector_ne_zero p)

def projectiveMap (F : Family J) (q : Φ.periodTorus) :
    Projectivization ℂ (Fin (F.projectiveDimension + 1) → ℂ) :=
  F.projectiveLift (Quotient.out q)

theorem projectiveLift_translate (F : Family J) (l : Φ.periodIntegerLattice) (p : Φ.space) :
    F.projectiveLift (p + l) = F.projectiveLift p := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨J.value l p ^ F.degree, ?_⟩
  funext i
  exact ((F.coordinate i).translates l p).symm

theorem projectiveMap_lift (F : Family J) (p : Φ.space) :
    F.projectiveMap (QuotientAddGroup.mk p) = F.projectiveLift p := by
  have hq : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk p : Φ.periodTorus)) : Φ.periodTorus) =
      QuotientAddGroup.mk p := Quotient.out_eq _
  have hl : Quotient.out (QuotientAddGroup.mk p : Φ.periodTorus) - p ∈ Φ.periodIntegerLattice :=
    QuotientAddGroup.eq_iff_sub_mem.mp hq
  let l : Φ.periodIntegerLattice := ⟨Quotient.out (QuotientAddGroup.mk p : Φ.periodTorus) - p, hl⟩
  have he : p + (l : Φ.space) = Quotient.out (QuotientAddGroup.mk p : Φ.periodTorus) := by dsimp [l]; abel
  simpa only [he, Family.projectiveMap] using F.projectiveLift_translate l p

theorem projectiveMap_continuous (F : Family J) : Continuous F.projectiveMap := by
  apply (QuotientAddGroup.isQuotientMap_mk Φ.periodIntegerLattice.toAddSubgroup).continuous_iff.mpr
  have hc : Continuous F.vector := continuous_pi (fun i => (F.coordinate i).continuous)
  have h := (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCompactness.continuous_projectivization_mk' ℂ (Fin (F.projectiveDimension + 1) → ℂ)).comp
    (hc.subtype_mk F.vector_ne_zero)
  convert! h using 1
  funext p
  exact F.projectiveMap_lift p

theorem projectiveMap_inPatch (F : Family J)
    (i : Fin (F.projectiveDimension + 1)) (p : Φ.space) :
    AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (F.projectiveMap (QuotientAddGroup.mk p)) ↔ F.coordinate i p ≠ 0 := by
  rw [F.projectiveMap_lift]
  exact AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_mk_iff i _ _

def chart (F : Family J) (i : Fin (F.projectiveDimension + 1)) (p : Φ.space) :
    Fin (F.projectiveDimension + 1) → ℂ := fun j => F.coordinate j p / F.coordinate i p

theorem projectiveMap_coordinates (F : Family J)
    (i : Fin (F.projectiveDimension + 1)) (p : Φ.space) :
    AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (F.projectiveMap (QuotientAddGroup.mk p)) = F.chart i p := by
  rw [F.projectiveMap_lift]
  rfl

theorem chart_contDiffAt (F : Family J)
    (i : Fin (F.projectiveDimension + 1)) (p : Φ.space) (hi : F.coordinate i p ≠ 0) :
    ContDiffAt ℂ 1 (F.chart i) p := by
  apply contDiffAt_pi.mpr
  intro j
  exact (F.coordinate j).regular.contDiffAt.div (F.coordinate i).regular.contDiffAt hi

theorem ratio_derivative_zero {n : ℕ} (s t : Section J n) (p v : Φ.space) (hs : s p ≠ 0)
    (hD : fderiv ℂ (fun z => t z / s z) p v = 0) :
    s p * fderiv ℂ t p v = t p * fderiv ℂ s p v := by
  have he : ((fun z => t z / s z) * (s : Φ.space → ℂ)) =ᶠ[nhds p] (t : Φ.space → ℂ) := by
    filter_upwards [s.continuous.continuousAt.eventually_ne hs] with z hz
    exact div_mul_cancel₀ _ hz
  have hds : DifferentiableAt ℂ (fun z => t z / s z) p :=
    (t.regular.contDiffAt.div s.regular.contDiffAt hs).differentiableAt (by norm_num)
  have he' := congrArg (fun L : Φ.space →L[ℂ] ℂ => L v) he.fderiv_eq
  rw [fderiv_mul hds (s.differentiable p)] at he'
  simp only [add_apply, smul_apply, smul_eq_mul, hD, mul_zero, add_zero] at he'
  rw [← he']
  field_simp [hs]

theorem chart_fderiv_component (F : Family J)
    (i j : Fin (F.projectiveDimension + 1)) (p v : Φ.space) (hi : F.coordinate i p ≠ 0) :
    fderiv ℂ (fun z => F.coordinate j z / F.coordinate i z) p v =
      (fderiv ℂ (F.chart i) p v) j := by
  have hd : DifferentiableAt ℂ (F.chart i) p := (F.chart_contDiffAt i p hi).differentiableAt (by norm_num)
  have he := fderiv_apply hd j
  exact congrArg (fun L : Φ.space →L[ℂ] ℂ => L v) he

theorem chart_fderiv_injective (F : Family J) (p : Φ.space)
    (hF : ∀ v : Φ.space, v ≠ 0 → F.Detects p v)
    (i : Fin (F.projectiveDimension + 1)) (hi : F.coordinate i p ≠ 0) :
    Function.Injective (fderiv ℂ (F.chart i) p) := by
  have hker (v : Φ.space) (hv : fderiv ℂ (F.chart i) p v = 0) : v = 0 := by
    by_contra hv0
    obtain ⟨s, hs, t, ht, _, hdet⟩ := hF v hv0
    obtain ⟨j, hj⟩ := F.coordinate_surjective s hs
    obtain ⟨k, hk⟩ := F.coordinate_surjective t ht
    have hzero (a : Fin (F.projectiveDimension + 1)) :
        fderiv ℂ (fun z => F.coordinate a z / F.coordinate i z) p v = 0 := by
      rw [F.chart_fderiv_component i a p v hi, hv]
      rfl
    have hsj := ratio_derivative_zero (F.coordinate i) (F.coordinate j) p v hi (hzero j)
    have htk := ratio_derivative_zero (F.coordinate i) (F.coordinate k) p v hi (hzero k)
    rw [hj] at hsj
    rw [hk] at htk
    have he : F.coordinate i p * (s p * fderiv ℂ t p v - t p * fderiv ℂ s p v) = 0 := by
      linear_combination (s p) * htk - (t p) * hsj
    exact hdet (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hi))
  intro u v huv
  apply sub_eq_zero.mp
  apply hker
  rw [map_sub, huv, sub_self]

theorem projectiveMap_eq_of_not_separates (F : Family J) (p q : Φ.space) :
    F.projectiveMap (QuotientAddGroup.mk p) = F.projectiveMap (QuotientAddGroup.mk q) ↔
      ¬F.Separates p q := by
  rw [F.projectiveMap_lift, F.projectiveMap_lift]
  rw [Family.projectiveLift, Family.projectiveLift, AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveZeroLocus.projectivization_mk_eq_iff_minors_eq]
  constructor
  · intro h hsep
    obtain ⟨s, hs, t, ht, hdet⟩ := hsep
    obtain ⟨i, hi⟩ := F.coordinate_surjective s hs
    obtain ⟨j, hj⟩ := F.coordinate_surjective t ht
    have he := h i j
    change F.coordinate i p * F.coordinate j q = F.coordinate j p * F.coordinate i q at he
    rw [hi, hj] at he
    exact hdet (by simpa only [mul_comm] using he)
  · intro h i j
    by_contra he
    apply h
    refine ⟨F.coordinate i, (F.indexEquiv.symm i).property,
      F.coordinate j, (F.indexEquiv.symm j).property, ?_⟩
    change F.coordinate i p * F.coordinate j q ≠ F.coordinate j p * F.coordinate i q at he
    simpa only [mul_comm] using he

end RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family

end

end OAI
