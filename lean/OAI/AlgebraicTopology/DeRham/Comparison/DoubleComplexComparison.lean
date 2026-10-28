import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexNormalization
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexAugmentation
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexQuasiIso

/-! # Double Complex Comparison -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexComparison.DoubleComplex

noncomputable section

/-!
# Comparison for an exact augmented first-quadrant double complex

An augmentation whose horizontal rows are exact induces a quasi-isomorphism
to the actual total complex. The proof produces cycle lifts and reflects
boundaries by finite horizontal elimination. Exactness, including at the
augmentation, is stated using the genuine differentials of the given
complexes; no comparison isomorphism is assumed.
-/

open _root_.CategoryTheory

universe u v

variable {R : Type u} [Ring R]
  (K : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))
  {A : CochainComplex (ModuleCat.{v} R) ℕ}
  (ε : A ⟶ K.X 0) (hε : ε ≫ K.d 0 1 = 0)

/-- The actual augmentation is supported in the zeroth horizontal column. -/
theorem augmentationToTotal_supported (n : ℕ) (a : A.X n) :
    DoubleComplexSupport.DoubleComplex.SupportedTo K n 0 ((DoubleComplexAugmentation.DoubleComplex.augmentationToTotal K ε hε).f n a) :=
  DoubleComplexSupport.DoubleComplex.supportedTo_iota K 0 n n (by simp) (ε.f n a)

/-- A cochain whose differential lies in the augmented column differs from
an augmented cochain by an actual total boundary. -/
theorem exists_augmentation_add_boundary
    (hzero : ∀ q : ℕ, Function.Exact (ε.f q) ((K.d 0 1).f q))
    (hexact : ∀ p q : ℕ, (K.flip.X q).ExactAt (p + 1))
    (n : ℕ) (x : (K.total (ComplexShape.up ℕ)).X n)
    (hd : DoubleComplexSupport.DoubleComplex.SupportedTo K (n + 1) 0
      ((K.total (ComplexShape.up ℕ)).d n (n + 1) x)) :
    ∃ a : A.X n, ∃ y : (K.total (ComplexShape.up ℕ)).X n.pred,
      x = (DoubleComplexAugmentation.DoubleComplex.augmentationToTotal K ε hε).f n a +
        (K.total (ComplexShape.up ℕ)).d n.pred n y := by
  obtain ⟨b, hb, y, hy⟩ := DoubleComplexNormalization.DoubleComplex.normalize K hexact n x hd
  obtain ⟨a, ha⟩ := (hzero n b).mp hb
  refine ⟨a, y, ?_⟩
  rw [DoubleComplexAugmentation.DoubleComplex.augmentationToTotal_f, ModuleCat.comp_apply, ha]
  exact hy

/-- Every total cocycle is cohomologous to the augmentation of a cocycle. -/
theorem augmentation_cycle_lift
    (hinj : ∀ q : ℕ, Function.Injective (ε.f q))
    (hzero : ∀ q : ℕ, Function.Exact (ε.f q) ((K.d 0 1).f q))
    (hexact : ∀ p q : ℕ, (K.flip.X q).ExactAt (p + 1))
    (n : ℕ) (x : (K.total (ComplexShape.up ℕ)).X n)
    (hx : (K.total (ComplexShape.up ℕ)).d n (n + 1) x = 0) :
    ∃ a : A.X n, A.d n (n + 1) a = 0 ∧
      ∃ y : (K.total (ComplexShape.up ℕ)).X n.pred,
        (K.total (ComplexShape.up ℕ)).d n.pred n y =
          (DoubleComplexAugmentation.DoubleComplex.augmentationToTotal K ε hε).f n a - x := by
  have hd : DoubleComplexSupport.DoubleComplex.SupportedTo K (n + 1) 0
      ((K.total (ComplexShape.up ℕ)).d n (n + 1) x) := by
    rw [hx]
    exact DoubleComplexSupport.DoubleComplex.supportedTo_zero K (n + 1) 0
  obtain ⟨a, y, hy⟩ := exists_augmentation_add_boundary K ε hε hzero hexact n x hd
  have hboundary := ConcreteCategory.congr_hom
    ((K.total (ComplexShape.up ℕ)).d_comp_d n.pred n (n + 1)) y
  change (K.total (ComplexShape.up ℕ)).d n (n + 1)
      ((K.total (ComplexShape.up ℕ)).d n.pred n y) = 0 at hboundary
  have hclosed : (K.total (ComplexShape.up ℕ)).d n (n + 1)
      ((DoubleComplexAugmentation.DoubleComplex.augmentationToTotal K ε hε).f n a) = 0 := by
    have h := congrArg ((K.total (ComplexShape.up ℕ)).d n (n + 1)) hy
    rw [hx, map_add, hboundary, add_zero] at h
    exact h.symm
  have hcomm := ConcreteCategory.congr_hom
    (DoubleComplexAugmentation.DoubleComplex.augmentationToTotal_comm K ε hε n (n + 1)) a
  have hsource : A.d n (n + 1) a = 0 := by
    apply DoubleComplexAugmentation.DoubleComplex.augmentationToTotal_f_injective K ε hε (n + 1) (hinj (n + 1))
    rw [map_zero]
    exact hcomm.symm.trans hclosed
  refine ⟨a, hsource, -y, ?_⟩
  rw [map_neg, hy]
  abel

/-- If an augmented cochain in positive degree is a total boundary, it is
already a boundary in the augmenting complex. -/
theorem augmentation_boundary_reflection_succ
    (hinj : ∀ q : ℕ, Function.Injective (ε.f q))
    (hzero : ∀ q : ℕ, Function.Exact (ε.f q) ((K.d 0 1).f q))
    (hexact : ∀ p q : ℕ, (K.flip.X q).ExactAt (p + 1))
    (n : ℕ) (a : A.X (n + 1)) (y : (K.total (ComplexShape.up ℕ)).X n)
    (hy : (K.total (ComplexShape.up ℕ)).d n (n + 1) y =
      (DoubleComplexAugmentation.DoubleComplex.augmentationToTotal K ε hε).f (n + 1) a) :
    ∃ c : A.X n, A.d n (n + 1) c = a := by
  have hd : DoubleComplexSupport.DoubleComplex.SupportedTo K (n + 1) 0
      ((K.total (ComplexShape.up ℕ)).d n (n + 1) y) := by
    rw [hy]
    exact augmentationToTotal_supported K ε hε (n + 1) a
  obtain ⟨c, z, hz⟩ := exists_augmentation_add_boundary K ε hε hzero hexact n y hd
  have hboundary := ConcreteCategory.congr_hom
    ((K.total (ComplexShape.up ℕ)).d_comp_d n.pred n (n + 1)) z
  change (K.total (ComplexShape.up ℕ)).d n (n + 1)
      ((K.total (ComplexShape.up ℕ)).d n.pred n z) = 0 at hboundary
  have hcomm := ConcreteCategory.congr_hom
    (DoubleComplexAugmentation.DoubleComplex.augmentationToTotal_comm K ε hε n (n + 1)) c
  refine ⟨c, DoubleComplexAugmentation.DoubleComplex.augmentationToTotal_f_injective K ε hε (n + 1) (hinj (n + 1)) ?_⟩
  calc
    (DoubleComplexAugmentation.DoubleComplex.augmentationToTotal K ε hε).f (n + 1) (A.d n (n + 1) c) =
        (K.total (ComplexShape.up ℕ)).d n (n + 1)
          ((DoubleComplexAugmentation.DoubleComplex.augmentationToTotal K ε hε).f n c) := hcomm.symm
    _ = (K.total (ComplexShape.up ℕ)).d n (n + 1) y := by
      rw [hz, map_add, hboundary, add_zero]
    _ = (DoubleComplexAugmentation.DoubleComplex.augmentationToTotal K ε hε).f (n + 1) a := hy

/-- There are no nonzero incoming boundaries in degree zero. In that degree
injectivity of the augmentation alone reflects a boundary. -/
theorem augmentation_boundary_reflection_zero
    (hinj : Function.Injective (ε.f 0)) (a : A.X 0)
    (hy : ∃ y : (K.total (ComplexShape.up ℕ)).X 0,
      (K.total (ComplexShape.up ℕ)).d 0 0 y = (DoubleComplexAugmentation.DoubleComplex.augmentationToTotal K ε hε).f 0 a) :
    ∃ c : A.X 0, A.d 0 0 c = a := by
  obtain ⟨y, hy⟩ := hy
  have hshape : (K.total (ComplexShape.up ℕ)).d 0 0 = 0 :=
    (K.total (ComplexShape.up ℕ)).shape 0 0 (by decide)
  have hzero : (DoubleComplexAugmentation.DoubleComplex.augmentationToTotal K ε hε).f 0 a = 0 := by
    rw [hshape] at hy
    exact hy.symm
  have ha : a = 0 := DoubleComplexAugmentation.DoubleComplex.augmentationToTotal_f_injective K ε hε 0 hinj
    (hzero.trans (map_zero _).symm)
  exact ⟨0, by rw [map_zero, ha]⟩

/-- An exact augmented first-quadrant double complex computes the cohomology
of its augmenting complex. This is the genuine native-total comparison map. -/
theorem augmentationToTotal_quasiIso
    (hinj : ∀ q : ℕ, Function.Injective (ε.f q))
    (hzero : ∀ q : ℕ, Function.Exact (ε.f q) ((K.d 0 1).f q))
    (hexact : ∀ p q : ℕ, (K.flip.X q).ExactAt (p + 1)) :
    QuasiIso (DoubleComplexAugmentation.DoubleComplex.augmentationToTotal K ε hε) := by
  apply DoubleComplexQuasiIso.DoubleComplex.quasiIso_of_cycle_lift_and_boundary_reflection
  · intro n
    have hp : (ComplexShape.up ℕ).prev n = n.pred := by
      cases n <;> simp
    let P (i j : ℕ) : Prop :=
      ∀ x : (K.total (ComplexShape.up ℕ)).X n,
        (K.total (ComplexShape.up ℕ)).d n j x = 0 →
        ∃ a : A.X n, A.d n j a = 0 ∧
          ∃ y : (K.total (ComplexShape.up ℕ)).X i,
            (K.total (ComplexShape.up ℕ)).d i n y =
              (DoubleComplexAugmentation.DoubleComplex.augmentationToTotal K ε hε).f n a - x
    have hP : P n.pred (n + 1) := augmentation_cycle_lift K ε hε hinj hzero hexact n
    exact (congrArg₂ P hp (CochainComplex.next ℕ n)).mpr hP
  · intro n
    have hp : (ComplexShape.up ℕ).prev n = n.pred := by
      cases n <;> simp
    let P (i : ℕ) : Prop :=
      ∀ a : A.X n, A.d n ((ComplexShape.up ℕ).next n) a = 0 →
        (∃ y : (K.total (ComplexShape.up ℕ)).X i,
          (K.total (ComplexShape.up ℕ)).d i n y = (DoubleComplexAugmentation.DoubleComplex.augmentationToTotal K ε hε).f n a) →
        ∃ c : A.X i, A.d i n c = a
    have hP : P n.pred := by
      intro a _ ha
      cases n with
      | zero =>
        exact augmentation_boundary_reflection_zero K ε hε (hinj 0) a ha
      | succ n =>
        obtain ⟨y, hy⟩ := ha
        exact augmentation_boundary_reflection_succ K ε hε hinj hzero hexact n a y hy
    exact (congrArg P hp).mpr hP

end

end OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexComparison.DoubleComplex
