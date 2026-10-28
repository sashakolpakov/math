import OAI.NumberTheory.PadicHodge.GeometricComparison.First.TwoOneInjection
import OAI.NumberTheory.PadicHodge.GeometricComparison.First.TwoZeroSurjectivity
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExtendLinearCore
import OAI.NumberTheory.PadicHodge.GeometricComparison.TrianglePrime
import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-! # Two Prime Torsion -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.First.TwoPrimeTorsion.FirstTwoComplex

noncomputable section

/-! A native low-degree reduction sequence and global constant lifting imply torsion-free degree-one derived sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Pretriangulated Opposite

variable (p : ℕ) [Fact p.Prime] (X : TopCat.{0})

local notation "V" => OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantSheaf.ConstantSheafSections.Sheaves ℤ_[p] X
local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantSheaf.ConstantSheafSections.coefficient ℤ_[p] X

local instance : HasDerivedCategory.{1} V := HasDerivedCategory.standard _

theorem truncated_torsionFree (K L : CochainComplex V ℕ) (f : K ⟶ L)
    (hz : ((p : ℤ_[p]) • 𝟙 K) ≫ f = 0)
    (he : ∀ n : ℕ, n ≤ 1 →
      ((ShortComplex.mk ((p : ℤ_[p]) • 𝟙 K) f hz).map
        (HomologicalComplex.eval V (.up ℕ) n)).ShortExact)
    (hf : Function.Surjective ((f.f 0).hom.app (op ⊤)))
    (hd : ∀ x : (K.X 0).obj.obj (op ⊤), (K.d 0 1).hom.app (op ⊤) x = 0) :
    Module.IsTorsionFree ℤ_[p]
      ((DerivedCategory.singleFunctor V 0).obj A ⟶
        (DerivedCategory.Q.obj (TwoZeroSurjectivity.FirstTwoComplex.integerComplex ℤ_[p] X K))⟦(1 : ℤ)⟧) := by
  let S := ShortComplex.mk ((p : ℤ_[p]) • 𝟙 K) f hz
  let F := TwoFunctor.FirstTwoComplex.functor V ⋙ ComplexShape.embeddingUpNat.extendFunctor V
  have hS : (S.map F).ShortExact :=
    ExtendShort.ExtendShortExact.shortExact _ _ (TwoFunctor.FirstTwoComplex.shortExact V S he)
  have hmap : DerivedCategory.Q.map (S.map F).f =
      (p : ℤ_[p]) • 𝟙 (DerivedCategory.Q.obj (TwoZeroSurjectivity.FirstTwoComplex.integerComplex ℤ_[p] X K)) := by
    change DerivedCategory.Q.map (F.map ((p : ℤ_[p]) • 𝟙 K)) = _
    rw [Functor.map_smul, CategoryTheory.Functor.map_id,
      Functor.map_smul, CategoryTheory.Functor.map_id]
    rfl
  apply TrianglePrime.TrianglePrimeTorsion.torsionFree p _ _ _
    (DerivedCategory.Q.map (TwoZeroSurjectivity.FirstTwoComplex.integerMap ℤ_[p] X f)) (DerivedCategory.triangleOfSESδ hS)
  · rw [← hmap]
    exact DerivedCategory.triangleOfSES_distinguished hS
  · exact TwoZeroSurjectivity.FirstTwoComplex.derived_hzero_surjective ℤ_[p] X f hf hd

theorem torsionFree (K L : CochainComplex V ℕ) (f : K ⟶ L)
    (hz : ((p : ℤ_[p]) • 𝟙 K) ≫ f = 0)
    (he : ∀ n : ℕ, n ≤ 1 →
      ((ShortComplex.mk ((p : ℤ_[p]) • 𝟙 K) f hz).map
        (HomologicalComplex.eval V (.up ℕ) n)).ShortExact)
    (hf : Function.Surjective ((f.f 0).hom.app (op ⊤)))
    (hd : ∀ x : (K.X 0).obj.obj (op ⊤), (K.d 0 1).hom.app (op ⊤) x = 0) :
    Module.IsTorsionFree ℤ_[p]
      ((DerivedCategory.singleFunctor V 0).obj A ⟶
        (DerivedCategory.Q.obj (K.extend ComplexShape.embeddingUpNat))⟦(1 : ℤ)⟧) := by
  let : Module.IsTorsionFree ℤ_[p]
      ((DerivedCategory.singleFunctor V 0).obj A ⟶
        (DerivedCategory.Q.obj ((TwoComplex.FirstTwoComplex.complex K).extend ComplexShape.embeddingUpNat))⟦(1 : ℤ)⟧) :=
    truncated_torsionFree p X K L f hz he hf hd
  apply PrimeTorsion.PrimeTorsionCriterion.torsionFree p
  intro x hx
  apply TwoOneInjection.FirstTwoComplex.hone_injective K A
  let g := (DerivedCategory.Q.map
    (HomologicalComplex.extendMap (TwoComplex.FirstTwoComplex.projection K) ComplexShape.embeddingUpNat))⟦(1 : ℤ)⟧'
  change x ≫ g = 0 ≫ g
  rw [zero_comp]
  have hpg : (p : ℤ_[p]) • (x ≫ g) = 0 := by
    rw [← Linear.smul_comp, hx, zero_comp]
  exact (smul_eq_zero.mp hpg).resolve_left
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.First.TwoPrimeTorsion.FirstTwoComplex
