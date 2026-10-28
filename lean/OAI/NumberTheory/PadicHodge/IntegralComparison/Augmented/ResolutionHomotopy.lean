import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionToInjective

/-! # Resolution Homotopy -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionHomotopy

noncomputable section

/-!
# IntegralComparison: comparison maps out of augmented resolutions are unique up to homotopy
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : CochainComplex C ℕ) {Z Z' : C} (ι : (CochainComplex.single₀ C).obj Z ⟶ K)
  [QuasiIso ι] (I : InjectiveResolution Z') (f : K ⟶ I.cocomplex) (hf : ι ≫ f = 0)

private def zero : K.X 1 ⟶ I.cocomplex.X 0 :=
  (ResolutionCycles.augmentation_exact_and_mono K ι).1.descToInjective
    (f.f 0) (congrArg (fun a => a.f 0) hf)

private theorem zero_comm : K.d 0 1 ≫ zero K ι I f hf = f.f 0 :=
  (ResolutionCycles.augmentation_exact_and_mono K ι).1.comp_descToInjective _ _

private def one : K.X 2 ⟶ I.cocomplex.X 1 :=
  (ResolutionCycles.positive_exact K ι 0).descToInjective
    (f.f 1 - zero K ι I f hf ≫ I.cocomplex.d 0 1) (by
      change K.d 0 1 ≫ (f.f 1 - zero K ι I f hf ≫ I.cocomplex.d 0 1) = 0
      rw [Preadditive.comp_sub, ← Category.assoc, zero_comm, f.comm, sub_self])

private theorem one_comm : K.d 1 2 ≫ one K ι I f hf =
    f.f 1 - zero K ι I f hf ≫ I.cocomplex.d 0 1 :=
  (ResolutionCycles.positive_exact K ι 0).comp_descToInjective _ _

private def step (i : ℕ) (a : K.X (i + 1) ⟶ I.cocomplex.X i)
    (b : K.X (i + 2) ⟶ I.cocomplex.X (i + 1))
    (h : f.f (i + 1) = K.d (i + 1) (i + 2) ≫ b + a ≫ I.cocomplex.d i (i + 1)) :
    K.X (i + 3) ⟶ I.cocomplex.X (i + 2) :=
  (ResolutionCycles.positive_exact K ι (i + 1)).descToInjective
    (f.f (i + 2) - b ≫ I.cocomplex.d (i + 1) (i + 2)) (by
      change K.d (i + 1) (i + 2) ≫ (f.f (i + 2) - b ≫ I.cocomplex.d (i + 1) (i + 2)) = 0
      rw [Preadditive.comp_sub, ← f.comm, h, Preadditive.add_comp, Category.assoc,
        Category.assoc, I.cocomplex.d_comp_d, comp_zero, add_zero, sub_self])

private theorem step_comm (i : ℕ) (a : K.X (i + 1) ⟶ I.cocomplex.X i)
    (b : K.X (i + 2) ⟶ I.cocomplex.X (i + 1))
    (h : f.f (i + 1) = K.d (i + 1) (i + 2) ≫ b + a ≫ I.cocomplex.d i (i + 1)) :
    K.d (i + 2) (i + 3) ≫ step K ι I f i a b h =
      f.f (i + 2) - b ≫ I.cocomplex.d (i + 1) (i + 2) :=
  (ResolutionCycles.positive_exact K ι (i + 1)).comp_descToInjective _ _

def homotopyZero : Homotopy f 0 :=
  Homotopy.mkCoinductive _ (zero K ι I f hf) (by simp only [zero_comm])
    (one K ι I f hf) (by rw [one_comm, add_comm, sub_add_cancel])
    (fun i ⟨a, b, h⟩ => ⟨step K ι I f i a b (by simpa only [add_comm] using h), by
      simp only [step_comm]
      abel⟩)

omit hf in
def homotopy (f' : K ⟶ I.cocomplex) (h : ι ≫ f = ι ≫ f') : Homotopy f f' :=
  Homotopy.equivSubZero.invFun (homotopyZero K ι I (f - f') (by
    rw [Preadditive.comp_sub, h, sub_self]))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionHomotopy
