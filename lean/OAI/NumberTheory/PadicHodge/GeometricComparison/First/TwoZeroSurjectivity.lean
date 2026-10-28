import OAI.NumberTheory.PadicHodge.GeometricComparison.First.TwoFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.ConnectiveSectionOn

/-! # Two Zero Surjectivity -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.First.TwoZeroSurjectivity.FirstTwoComplex

noncomputable section

/-! Surjectivity in derived degree zero for the actual first-two-term reduction map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

variable (R : Type) [CommRing R] (X : TopCat.{0})

local notation "V" => OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantSheaf.ConstantSheafSections.Sheaves R X
local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantSheaf.ConstantSheafSections.coefficient R X

local instance : HasDerivedCategory.{1} V := HasDerivedCategory.standard _

def integerComplex (K : CochainComplex V ℕ) : CochainComplex V ℤ :=
  (TwoComplex.FirstTwoComplex.complex K).extend ComplexShape.embeddingUpNat

def integerMap {K L : CochainComplex V ℕ} (f : K ⟶ L) :
    integerComplex R X K ⟶ integerComplex R X L :=
  HomologicalComplex.extendMap (TwoComplex.FirstTwoComplex.map f) ComplexShape.embeddingUpNat

instance integer_connective (K : CochainComplex V ℕ) : (integerComplex R X K).IsStrictlyGE 0 := by
  change CochainComplex.IsStrictlyGE ((TwoComplex.FirstTwoComplex.complex K).extend ComplexShape.embeddingUpNat) 0
  infer_instance

def integerTermIso (K : CochainComplex V ℕ) (n : ℕ) :
    (integerComplex R X K).X (n : ℤ) ≅ (TwoComplex.FirstTwoComplex.complex K).X n :=
  (TwoComplex.FirstTwoComplex.complex K).extendXIso ComplexShape.embeddingUpNat rfl

theorem integer_zero_surjective {K L : CochainComplex V ℕ} (f : K ⟶ L)
    (hf : Function.Surjective ((f.f 0).hom.app (op ⊤))) :
    Function.Surjective (((integerMap R X f).f 0).hom.app (op ⊤)) := by
  let F := (sheafSections (Opens.grothendieckTopology X) (ModuleCat R)).obj (op ⊤)
  let : Epi (F.map ((TwoComplex.FirstTwoComplex.map f).f 0)) := (ModuleCat.epi_iff_surjective _).mpr hf
  have he : (integerMap R X f).f 0 =
      (integerTermIso R X K 0).hom ≫ (TwoComplex.FirstTwoComplex.map f).f 0 ≫ (integerTermIso R X L 0).inv :=
    HomologicalComplex.extendMap_f (TwoComplex.FirstTwoComplex.map f) ComplexShape.embeddingUpNat rfl
  apply (ModuleCat.epi_iff_surjective _).mp
  change Epi (F.map ((integerMap R X f).f 0))
  rw [he, F.map_comp, F.map_comp]
  infer_instance

theorem integer_differential_zero (K : CochainComplex V ℕ)
    (hd : ∀ x : (K.X 0).obj.obj (op ⊤), (K.d 0 1).hom.app (op ⊤) x = 0)
    (x : ((integerComplex R X K).X 0).obj.obj (op ⊤)) :
    ((integerComplex R X K).d 0 1).hom.app (op ⊤) x = 0 := by
  have he : (integerComplex R X K).d 0 1 =
      (integerTermIso R X K 0).hom ≫ (TwoComplex.FirstTwoComplex.complex K).d 0 1 ≫ (integerTermIso R X K 1).inv :=
    (TwoComplex.FirstTwoComplex.complex K).extend_d_eq ComplexShape.embeddingUpNat (i := 0) (j := 1) rfl rfl
  rw [he]
  change (integerTermIso R X K 1).inv.hom.app (op ⊤)
    ((K.d 0 1).hom.app (op ⊤) ((integerTermIso R X K 0).hom.hom.app (op ⊤) x)) = 0
  erw [hd, map_zero]

theorem derived_hzero_surjective {K L : CochainComplex V ℕ} (f : K ⟶ L)
    (hf : Function.Surjective ((f.f 0).hom.app (op ⊤)))
    (hd : ∀ x : (K.X 0).obj.obj (op ⊤), (K.d 0 1).hom.app (op ⊤) x = 0) :
    Function.Surjective
      (fun a : (DerivedCategory.singleFunctor V 0).obj A ⟶
          DerivedCategory.Q.obj (integerComplex R X K) =>
        a ≫ DerivedCategory.Q.map (integerMap R X f)) :=
  ConnectiveSectionOn.ConnectiveSectionSurjectivity.surjective R X _ _ (integerMap R X f)
    (integer_zero_surjective R X f hf) (integer_differential_zero R X K hd)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.First.TwoZeroSurjectivity.FirstTwoComplex
