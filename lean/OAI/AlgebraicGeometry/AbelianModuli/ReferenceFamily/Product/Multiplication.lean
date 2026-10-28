import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CupUnitNaturality
import OAI.AlgebraicGeometry.AbelianVariety.ProductSpanning
import OAI.AlgebraicGeometry.AbelianVariety.DoublingDifference

/-! # Multiplication -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.Multiplication

noncomputable section

section

/-! The actual H1 of the point-space product is the sum of the two
projection pullbacks, proved using the native normalized Künneth theorem. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.CupPullbackSingular.Construction.CupPullback

def productH1Left (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : A.variety.rationalCohomology 1 →ₗ[ℚ]
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointProductTop A) 1 :=
  (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
    (TopCat.prodFst (X := AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) (Y := AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)) 1).hom

def productH1Right (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : A.variety.rationalCohomology 1 →ₗ[ℚ]
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointProductTop A) 1 :=
  (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
    (TopCat.prodSnd (X := AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) (Y := AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)) 1).hom

theorem productH1_cross_zero_left (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : A.variety.rationalCohomology 0) (b : A.variety.rationalCohomology 1) :
    AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointProductTop A) 0 1
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) TopCat.prodFst 0 a)
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) TopCat.prodSnd 1 b) =
      productH1Right A (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 0 1 a b) :=
  (congrArg (fun c => AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointProductTop A) 0 1 c
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) TopCat.prodSnd 1 b))
      (CupUnitNaturality.abelianH0_pullbacks_eq A TopCat.prodFst TopCat.prodSnd a)).trans
    (AlgebraicTopology.Kunneth.CupPullbackSingular.Construction.CupPullback.singularCohomologyCup_pullback (TopCat.prodSnd (X := AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) (Y := AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)) 0 1 a b).symm

theorem productH1_cross_zero_right (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : A.variety.rationalCohomology 1) (b : A.variety.rationalCohomology 0) :
    AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointProductTop A) 1 0
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) TopCat.prodFst 1 a)
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) TopCat.prodSnd 0 b) =
      productH1Left A (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 1 0 a b) :=
  (congrArg (fun c => AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointProductTop A) 1 0
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) TopCat.prodFst 1 a) c)
      (CupUnitNaturality.abelianH0_pullbacks_eq A TopCat.prodSnd TopCat.prodFst b)).trans
    (AlgebraicTopology.Kunneth.CupPullbackSingular.Construction.CupPullback.singularCohomologyCup_pullback (TopCat.prodFst (X := AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) (Y := AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)) 1 0 a b).symm

theorem productH1_ranges_top (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    LinearMap.range (productH1Left A) ⊔ LinearMap.range (productH1Right A) = ⊤ := by
  apply AbelianVariety.ProductSpanning.Constructions.ExteriorCohomology.abelianProduct_cohomology_spanned A 1
  intro p q hpq a b
  have hp : p = 0 ∨ p = 1 := by omega
  rcases hp with rfl | rfl
  · have hq : q = 1 := by omega
    subst q
    change AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointProductTop A) 0 1 _ _ ∈ _
    have h : productH1Right A (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 0 1 a b) ∈
        LinearMap.range (productH1Left A) ⊔ LinearMap.range (productH1Right A) :=
      (show LinearMap.range (productH1Right A) ≤
        LinearMap.range (productH1Left A) ⊔ LinearMap.range (productH1Right A) from le_sup_right)
          (LinearMap.mem_range_self _ _)
    exact (productH1_cross_zero_left A a b).symm ▸ h
  · have hq : q = 0 := by omega
    subst q
    change AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointProductTop A) 1 0 _ _ ∈ _
    have h : productH1Left A (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 1 0 a b) ∈
        LinearMap.range (productH1Left A) ⊔ LinearMap.range (productH1Right A) :=
      (show LinearMap.range (productH1Left A) ≤
        LinearMap.range (productH1Left A) ⊔ LinearMap.range (productH1Right A) from le_sup_left)
          (LinearMap.mem_range_self _ _)
    exact (productH1_cross_zero_right A a b).symm ▸ h

theorem productH1_decomposition (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointProductTop A) 1) :
    ∃ a b : A.variety.rationalCohomology 1, c = productH1Left A a + productH1Right A b := by
  have hc : c ∈ LinearMap.range (productH1Left A) ⊔ LinearMap.range (productH1Right A) :=
    (productH1_ranges_top A).symm ▸ Submodule.mem_top
  obtain ⟨x, ⟨a, rfl⟩, y, ⟨b, rfl⟩, h⟩ := Submodule.mem_sup.mp hc
  exact ⟨a, b, h.symm⟩

end

/-! Degree-one classes are primitive for the actual abelian group
multiplication, by the native product decomposition and the two axes. -/

open _root_.CategoryTheory

theorem abelianH1_multiplication (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (c : A.variety.rationalCohomology 1) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop A) 1 c =
      productH1Left A c + productH1Right A c := by
  obtain ⟨a, b, hab⟩ := productH1_decomposition A
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop A) 1 c)
  have ha := congrArg (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
    (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianInsertFirstTop A) 1) hab
  have hb := congrArg (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
    (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianInsertSecondTop A) 1) hab
  simp only [map_add, productH1Left, productH1Right, AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.pullback_comp_apply,
    AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.first_mul, AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.first_fst, AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.first_snd, AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_id,
    ConcreteCategory.id_apply, AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPowTop_pullback, Nat.cast_zero,
    pow_one, zero_smul, add_zero] at ha
  simp only [map_add, productH1Left, productH1Right, AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.pullback_comp_apply,
    AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.second_mul, AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.second_fst, AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.second_snd, AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_id,
    ConcreteCategory.id_apply, AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPowTop_pullback, Nat.cast_zero,
    pow_one, zero_smul, zero_add] at hb
  exact hab.trans (congrArg₂ (fun x y => productH1Left A x + productH1Right A y) ha.symm hb.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.Multiplication
