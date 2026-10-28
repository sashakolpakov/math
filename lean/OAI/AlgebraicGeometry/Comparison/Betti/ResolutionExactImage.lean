import Mathlib
import OAI.Analysis.DifferentialForms.Manifold.CochainAugmentation

/-! # Resolution Exact Image -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ResolutionExactImage

noncomputable section

section

/-!
# Comparing a proved resolution with an injective resolution

The source consists of an actual complex with a proved kernel augmentation
and proved positive-degree exactness. The comparison extends the original
augmentation by injectivity, following the standard degreewise construction
of `InjectiveResolution.desc`, without assuming injectivity of the source.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C : Type*} [Category* C] [Abelian C]

structure Data (Z : C) where
  complex : CochainComplex C ℕ
  augmentation : Z ⟶ complex.X 0
  augmentation_d : augmentation ≫ complex.d 0 1 = 0
  isKernel : IsLimit (KernelFork.ofι augmentation augmentation_d)
  exact_succ : ∀ n, complex.ExactAt (n + 1)

variable {Z : C} (R : Data Z) (I : InjectiveResolution Z)

instance augmentation_mono : Mono R.augmentation := mono_of_isLimit_fork R.isKernel

def cochainAugmentation : (CochainComplex.single₀ C).obj Z ⟶ R.complex :=
  (CochainComplex.fromSingle₀Equiv R.complex Z).symm ⟨R.augmentation, R.augmentation_d⟩

instance cochainAugmentation_quasiIso : QuasiIso (cochainAugmentation R) :=
  Analysis.DifferentialForms.Manifold.CochainAugmentation.cochainAugmentation_quasiIso R.complex R.augmentation R.augmentation_d R.isKernel R.exact_succ

def zeroMap : R.complex.X 0 ⟶ I.cocomplex.X 0 :=
  Injective.factorThru (show Z ⟶ I.cocomplex.X 0 from I.ι.f 0) R.augmentation

theorem augmentation_zeroMap : R.augmentation ≫ zeroMap R I = I.ι.f 0 :=
  Injective.comp_factorThru (show Z ⟶ I.cocomplex.X 0 from I.ι.f 0) R.augmentation

def oneMap : R.complex.X 1 ⟶ I.cocomplex.X 1 :=
  (ShortComplex.exact_of_f_is_kernel
    (ShortComplex.mk R.augmentation (R.complex.d 0 1) R.augmentation_d) R.isKernel).descToInjective
      (zeroMap R I ≫ I.cocomplex.d 0 1) (by
        rw [← Category.assoc, augmentation_zeroMap]
        exact I.ι_f_zero_comp_complex_d)

theorem oneMap_comm : R.complex.d 0 1 ≫ oneMap R I = zeroMap R I ≫ I.cocomplex.d 0 1 := by
  unfold oneMap
  exact (ShortComplex.exact_of_f_is_kernel
    (ShortComplex.mk R.augmentation (R.complex.d 0 1) R.augmentation_d) R.isKernel).comp_descToInjective _ _

theorem exact_next (n : ℕ) :
    (ShortComplex.mk (R.complex.d n (n + 1)) (R.complex.d (n + 1) (n + 2))
      (R.complex.d_comp_d n (n + 1) (n + 2))).Exact :=
  (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp)
    (by simp only [CochainComplex.next]; rfl)).1 (R.exact_succ n)

def nextMap (n : ℕ) (g : R.complex.X n ⟶ I.cocomplex.X n)
    (g' : R.complex.X (n + 1) ⟶ I.cocomplex.X (n + 1))
    (w : R.complex.d n (n + 1) ≫ g' = g ≫ I.cocomplex.d n (n + 1)) :
    Σ' g'' : R.complex.X (n + 2) ⟶ I.cocomplex.X (n + 2),
      R.complex.d (n + 1) (n + 2) ≫ g'' = g' ≫ I.cocomplex.d (n + 1) (n + 2) :=
  ⟨(exact_next R n).descToInjective (g' ≫ I.cocomplex.d (n + 1) (n + 2)) (by
      rw [← Category.assoc, w, Category.assoc, I.cocomplex.d_comp_d, comp_zero]),
    (exact_next R n).comp_descToInjective _ _⟩

/-- An actual cochain map extending the given augmentation. -/
def toInjective : R.complex ⟶ I.cocomplex :=
  CochainComplex.mkHom _ _ (zeroMap R I) (oneMap R I) (oneMap_comm R I).symm
    (fun n ⟨g, g', w⟩ => ⟨(nextMap R I n g g' w.symm).1, (nextMap R I n g g' w.symm).2.symm⟩)

theorem toInjective_normalization : cochainAugmentation R ≫ toInjective R I = I.ι := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
    simp only [HomologicalComplex.comp_f, cochainAugmentation,
      CochainComplex.fromSingle₀Equiv_symm_apply_f_zero, toInjective, CochainComplex.mkHom_f_0]
    exact augmentation_zeroMap R I
  | succ n =>
    exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 Z (n + 1) (by omega)).eq_of_src _ _

/-- The constructed comparison is a quasi-isomorphism because both augmentations are resolutions. -/
theorem toInjective_quasiIso : QuasiIso (toInjective R I) := by
  have : QuasiIso (cochainAugmentation R ≫ toInjective R I) := by
    rw [toInjective_normalization]
    infer_instance
  exact quasiIso_of_comp_left (cochainAugmentation R) (toInjective R I)

end

/-! Exact functors carry genuine resolutions to genuine resolutions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C : Type*} [Category* C] [Abelian C] {Z : C}

def ofInjective (I : InjectiveResolution Z) : Data Z where
  complex := I.cocomplex
  augmentation := I.ι.f 0
  augmentation_d := I.ι_f_zero_comp_complex_d
  isKernel := I.isLimitKernelFork
  exact_succ := I.cocomplex_exactAt_succ

def changeSource (R : Data Z) {W : C} (e : W ≅ Z) : Data W where
  complex := R.complex
  augmentation := e.hom ≫ R.augmentation
  augmentation_d := by rw [Category.assoc, R.augmentation_d, comp_zero]
  isKernel := IsLimit.ofIsoLimit R.isKernel (Fork.ext e.symm (by
    change e.inv ≫ (e.hom ≫ R.augmentation) = R.augmentation
    exact e.inv_hom_id_assoc _))
  exact_succ := R.exact_succ

variable {D : Type*} [Category* D] [Abelian D]
  (R : Data Z) (F : C ⥤ D) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

def exactImage : Data (F.obj Z) where
  complex := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.complex
  augmentation := F.map R.augmentation
  augmentation_d := by
    change F.map R.augmentation ≫ F.map (R.complex.d 0 1) = 0
    rw [← F.map_comp, R.augmentation_d, F.map_zero]
  isKernel := KernelFork.mapIsLimit _ R.isKernel F
  exact_succ n := by
    change ((R.complex.sc (n + 1)).map F).Exact
    exact ((HomologicalComplex.exactAt_iff _ _).mp (R.exact_succ n)).map F

end

end OAI.AlgebraicGeometry.Comparison.Betti.ResolutionExactImage
