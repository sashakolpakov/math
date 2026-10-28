import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ThomResolutionDiagram
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-! # Resolution Homotopy -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions

noncomputable section

section

/-! Actual maps from a degree-zero sheaf resolution to an independent injective resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable {C : Type*} [Category C] [Abelian C]
variable (K : CochainComplex C ℕ)

def zeroAugmentationSequence : ShortComplex C :=
  ShortComplex.mk ((ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation K).f 0) (K.d 0 1) (by
    rw [ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation_f_zero, Category.assoc, K.iCycles_d, comp_zero])

theorem zeroAugmentationSequence_exact : (zeroAugmentationSequence K).Exact := by
  let S := ShortComplex.mk (K.iCycles 0) (K.d 0 1) (K.iCycles_d 0 1)
  have hS : S.Exact := ShortComplex.exact_of_f_is_kernel S (K.cyclesIsKernel 0 1 (by simp))
  let e : S ≅ zeroAugmentationSequence K := ShortComplex.isoMk K.isoHomologyπ₀
    (Iso.refl _) (Iso.refl _)
    (by simp [S, zeroAugmentationSequence, ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation_f_zero])
    (by simp [S, zeroAugmentationSequence])
  exact ShortComplex.exact_of_iso e hS

theorem cochainZeroHomologyAugmentation_zero_mono : Mono ((ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation K).f 0) := by
  rw [ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation_f_zero]
  infer_instance

variable (hK : ∀ n, K.ExactAt (n+1)) (I : InjectiveResolution (K.homology 0))

def resolutionLiftZero : K.X 0 ⟶ I.cocomplex.X 0 := by
  have := cochainZeroHomologyAugmentation_zero_mono K
  exact Injective.factorThru (I.ι.f 0) ((ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation K).f 0)

theorem resolutionLiftZero_comm :
    (ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation K).f 0 ≫ resolutionLiftZero K I = I.ι.f 0 := by
  have := cochainZeroHomologyAugmentation_zero_mono K
  exact Injective.comp_factorThru _ _

def resolutionLiftOne : K.X 1 ⟶ I.cocomplex.X 1 :=
  (zeroAugmentationSequence_exact K).descToInjective
    (resolutionLiftZero K I ≫ I.cocomplex.d 0 1) (by
      change (ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation K).f 0 ≫
        (resolutionLiftZero K I ≫ I.cocomplex.d 0 1) = 0
      rw [← Category.assoc, resolutionLiftZero_comm, I.ι_f_zero_comp_complex_d])

theorem resolutionLiftOne_comm :
    K.d 0 1 ≫ resolutionLiftOne K I = resolutionLiftZero K I ≫ I.cocomplex.d 0 1 :=
  (zeroAugmentationSequence_exact K).comp_descToInjective _ _

def resolutionLiftSuccessor (n : ℕ)
    (g : K.X n ⟶ I.cocomplex.X n) (g' : K.X (n+1) ⟶ I.cocomplex.X (n+1))
    (w : K.d n (n+1) ≫ g' = g ≫ I.cocomplex.d n (n+1)) :
    Σ' g'' : K.X (n+2) ⟶ I.cocomplex.X (n+2),
      K.d (n+1) (n+2) ≫ g'' = g' ≫ I.cocomplex.d (n+1) (n+2) := by
  have he : (ShortComplex.mk _ _ (K.d_comp_d n (n+1) (n+2))).Exact :=
    (HomologicalComplex.exactAt_iff' _ n (n+1) (n+2) (by simp)
      (by simp only [CochainComplex.next]; rfl)).mp (hK n)
  exact ⟨he.descToInjective (g' ≫ I.cocomplex.d (n+1) (n+2)) (by
    rw [← Category.assoc, w, Category.assoc, I.cocomplex.d_comp_d, comp_zero]),
      he.comp_descToInjective _ _⟩

def resolutionLift : K ⟶ I.cocomplex :=
  CochainComplex.mkHom _ _ (resolutionLiftZero K I) (resolutionLiftOne K I)
    (resolutionLiftOne_comm K I).symm
    (fun n ⟨g,g',w⟩ => ⟨(resolutionLiftSuccessor K hK I n g g' w.symm).1,
      (resolutionLiftSuccessor K hK I n g g' w.symm).2.symm⟩)

theorem resolutionLift_augmentation :
    ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation K ≫ resolutionLift K hK I = I.ι := by
  apply (CochainComplex.fromSingle₀Equiv I.cocomplex (K.homology 0)).injective
  apply Subtype.ext
  change (ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation K).f 0 ≫ (resolutionLift K hK I).f 0 = I.ι.f 0
  exact resolutionLiftZero_comm K I

theorem resolutionLift_quasiIso : QuasiIso (resolutionLift K hK I) := by
  have : QuasiIso (ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation K) :=
    ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation_quasiIso K (by
      intro n hn
      cases n with
      | zero => omega
      | succ n => exact (hK n).isZero_homology)
  have : QuasiIso (ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation K ≫ resolutionLift K hK I) := by
    rw [resolutionLift_augmentation]
    infer_instance
  exact quasiIso_of_comp_left (ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation K) (resolutionLift K hK I)

end

/-! Maps from an actual degree-zero resolution to an injective complex are unique up to actual homotopy. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive

set_option backward.isDefEq.respectTransparency false

variable {C : Type*} [Category C] [Abelian C]
variable (K L : CochainComplex C ℕ) (hK : ∀ n, K.ExactAt (n+1))
variable [∀ n, Injective (L.X n)]

include hK in
theorem resolutionSuccessorSequence_exact (n : ℕ) :
    (ShortComplex.mk _ _ (K.d_comp_d n (n+1) (n+2))).Exact :=
  (HomologicalComplex.exactAt_iff' _ n (n+1) (n+2) (by simp)
    (by simp only [CochainComplex.next]; rfl)).mp (hK n)

variable (f : K ⟶ L) (hf : ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation K ≫ f = 0)

def resolutionNullHomotopyZero : K.X 1 ⟶ L.X 0 :=
  (zeroAugmentationSequence_exact K).descToInjective (f.f 0)
    (congrArg (fun f => f.f 0) hf)

@[reassoc (attr := simp)]
theorem resolutionNullHomotopyZero_comp :
    K.d 0 1 ≫ resolutionNullHomotopyZero K L f hf = f.f 0 :=
  (zeroAugmentationSequence_exact K).comp_descToInjective _ _

def resolutionNullHomotopyOne : K.X 2 ⟶ L.X 1 :=
  (resolutionSuccessorSequence_exact K hK 0).descToInjective
    (f.f 1 - resolutionNullHomotopyZero K L f hf ≫ L.d 0 1) (by
      rw [comp_sub, resolutionNullHomotopyZero_comp_assoc, f.comm, sub_self])

@[reassoc (attr := simp)]
theorem resolutionNullHomotopyOne_comp :
    K.d 1 2 ≫ resolutionNullHomotopyOne K L hK f hf =
      f.f 1 - resolutionNullHomotopyZero K L f hf ≫ L.d 0 1 :=
  (resolutionSuccessorSequence_exact K hK 0).comp_descToInjective _ _

def resolutionNullHomotopySuccessor (n : ℕ)
    (g : K.X (n+1) ⟶ L.X n) (g' : K.X (n+2) ⟶ L.X (n+1))
    (w : f.f (n+1) = K.d (n+1) (n+2) ≫ g' + g ≫ L.d n (n+1)) :
    K.X (n+3) ⟶ L.X (n+2) :=
  (resolutionSuccessorSequence_exact K hK (n+1)).descToInjective
    (f.f (n+2) - g' ≫ L.d (n+1) (n+2)) (by
      dsimp
      rw [comp_sub, ← f.comm, w, add_comp, Category.assoc, Category.assoc,
        L.d_comp_d, comp_zero, add_zero, sub_self])

@[reassoc (attr := simp)]
theorem resolutionNullHomotopySuccessor_comp (n : ℕ)
    (g : K.X (n+1) ⟶ L.X n) (g' : K.X (n+2) ⟶ L.X (n+1))
    (w : f.f (n+1) = K.d (n+1) (n+2) ≫ g' + g ≫ L.d n (n+1)) :
    K.d (n+2) (n+3) ≫ resolutionNullHomotopySuccessor K L hK f n g g' w =
      f.f (n+2) - g' ≫ L.d (n+1) (n+2) :=
  (resolutionSuccessorSequence_exact K hK (n+1)).comp_descToInjective _ _

def resolutionNullHomotopy : Homotopy f 0 :=
  Homotopy.mkCoinductive f (resolutionNullHomotopyZero K L f hf) (by simp)
    (resolutionNullHomotopyOne K L hK f hf) (by simp)
    (fun n ⟨g,g',w⟩ =>
      ⟨resolutionNullHomotopySuccessor K L hK f n g g' (by simpa only [add_comm] using w), by simp⟩)

def resolutionHomotopy (f g : K ⟶ L)
    (hfg : ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation K ≫ f = ThomGoodShiftFlasque.Constructions.cochainZeroHomologyAugmentation K ≫ g) :
    Homotopy f g :=
  Homotopy.equivSubZero.invFun (resolutionNullHomotopy K L hK (f-g) (by
    rw [comp_sub, hfg, sub_self]))

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions
