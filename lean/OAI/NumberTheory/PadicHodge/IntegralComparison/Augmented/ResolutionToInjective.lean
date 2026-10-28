import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

/-! # Resolution To Injective -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionToInjective

noncomputable section

/-!
# IntegralComparison: comparison from an actual augmented resolution to an injective resolution
-/

open _root_.CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : CochainComplex C ℕ) {Z Z' : C} (ι : (CochainComplex.single₀ C).obj Z ⟶ K)
  [QuasiIso ι] (I : InjectiveResolution Z') (f : Z ⟶ Z')

local notation "aK" => OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.augmentation K ι
local notation "aI" => OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.augmentation I.cocomplex I.ι

private def zero : K.X 0 ⟶ I.cocomplex.X 0 := by
  letI : Mono aK := (ResolutionCycles.augmentation_exact_and_mono K ι).2
  exact Injective.factorThru (f ≫ aI) aK

private theorem zero_comm : aK ≫ zero K ι I f = f ≫ aI := by
  let : Mono aK := (ResolutionCycles.augmentation_exact_and_mono K ι).2
  exact Injective.comp_factorThru (f ≫ aI) aK

private def one : K.X 1 ⟶ I.cocomplex.X 1 :=
  (ResolutionCycles.augmentation_exact_and_mono K ι).1.descToInjective
    (zero K ι I f ≫ I.cocomplex.d 0 1) (by
      change aK ≫ zero K ι I f ≫ I.cocomplex.d 0 1 = 0
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun a => a ≫ I.cocomplex.d 0 1) (zero_comm K ι I f)).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun a => f ≫ a) (ResolutionCycles.augmentation_condition I.cocomplex I.ι)).trans
              Limits.comp_zero))))

private theorem one_comm : K.d 0 1 ≫ one K ι I f = zero K ι I f ≫ I.cocomplex.d 0 1 :=
  (ResolutionCycles.augmentation_exact_and_mono K ι).1.comp_descToInjective _ _

private def step (i : ℕ) (a : K.X i ⟶ I.cocomplex.X i)
    (b : K.X (i + 1) ⟶ I.cocomplex.X (i + 1))
    (h : K.d i (i + 1) ≫ b = a ≫ I.cocomplex.d i (i + 1)) :
    Σ' c : K.X (i + 2) ⟶ I.cocomplex.X (i + 2),
      K.d (i + 1) (i + 2) ≫ c = b ≫ I.cocomplex.d (i + 1) (i + 2) :=
  ⟨(ResolutionCycles.positive_exact K ι i).descToInjective
    (b ≫ I.cocomplex.d (i + 1) (i + 2)) (by
      change K.d i (i + 1) ≫ b ≫ I.cocomplex.d (i + 1) (i + 2) = 0
      rw [← Category.assoc, h, Category.assoc, I.cocomplex.d_comp_d, Limits.comp_zero]),
    (ResolutionCycles.positive_exact K ι i).comp_descToInjective _ _⟩

def map : K ⟶ I.cocomplex :=
  CochainComplex.mkHom _ _ (zero K ι I f) (one K ι I f) (one_comm K ι I f).symm
    (fun i ⟨a, b, h⟩ => ⟨(step K ι I i a b h.symm).1, (step K ι I i a b h.symm).2.symm⟩)

theorem augmentation_zero : aK ≫ (ResolutionToInjective.map K ι I f).f 0 = f ≫ aI := zero_comm K ι I f

theorem augmentation : ι ≫ ResolutionToInjective.map K ι I f = (CochainComplex.single₀ C).map f ≫ I.ι := by
  apply (CochainComplex.fromSingle₀Equiv I.cocomplex Z).injective
  apply Subtype.ext
  exact (augmentation_zero K ι I f).trans
    (congrArg (fun a => a ≫ aI) (CochainComplex.single₀_map_f_zero f)).symm

theorem quasiIso [IsIso f] : QuasiIso (ResolutionToInjective.map K ι I f) := by
  have : QuasiIso (ι ≫ ResolutionToInjective.map K ι I f) := by
    rw [augmentation]
    infer_instance
  exact quasiIso_of_comp_left ι (ResolutionToInjective.map K ι I f)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionToInjective
