import OAI.AlgebraicTopology.Kunneth.ComparisonLow
import OAI.AlgebraicTopology.Kunneth.ProjectiveFinitenessLe
import Mathlib.LinearAlgebra.Contraction

/-! # Cohomology Tensor Ne -/

namespace OAI.AlgebraicTopology.Kunneth.CohomologyTensorNe

noncomputable section

section

/-! Dualizing the homological Künneth decomposition over a field. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct DirectSum

namespace Construction.CohomologyDecomposition

open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

def degreePairsEquiv (n : ℕ) : Fin (n + 1) ≃ TensorHomologyD.Construction.TensorHomology.DegreePairs n where
  toFun i := ⟨(i.val, n - i.val), by have := i.isLt; omega⟩
  invFun ij := ⟨ij.val.1, by have := ij.property; omega⟩
  left_inv i := Fin.ext rfl
  right_inv ij := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have := ij.property
      dsimp
      omega

instance degreePairsFintype (n : ℕ) : Fintype (TensorHomologyD.Construction.TensorHomology.DegreePairs n) :=
  Fintype.ofEquiv (Fin (n + 1)) (degreePairsEquiv n)

variable {k : Type} [Field k]

/-- A finite sum of dual spaces is the dual of the finite direct sum. -/
def directSumDualEquiv {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → Type)
    [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)] :
    (⨁ i, Module.Dual k (M i)) ≃ₗ[k] Module.Dual k (⨁ i, M i) :=
  (DirectSum.linearEquivFunOnFintype k ι (fun i => Module.Dual k (M i))).trans
    (DFinsupp.lsum k)

abbrev CohomologySum (X Y : TopCat.{0}) (n : ℕ) :=
  ⨁ ij : TensorHomologyD.Construction.TensorHomology.DegreePairs n,
    Cohomology.Singular.Basic.singularCohomology (ModuleCat.of k k) X ij.val.1 ⊗[k]
      Cohomology.Singular.Basic.singularCohomology (ModuleCat.of k k) Y ij.val.2

variable (X Y : TopCat.{0})
variable [∀ n, FiniteDimensional k ((Cohomology.Singular.Evaluation.singularScalarChains (R := k) X).homology n)]
variable [∀ n, FiniteDimensional k ((Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y).homology n)]

/-- First dualize each tensor summand, using the canonical evaluation pairing. -/
def cohomologySumDualEquiv (n : ℕ) :
    CohomologySum (k := k) X Y n ≃ₗ[k]
      Module.Dual k (⨁ ij : TensorHomologyD.Construction.TensorHomology.DegreePairs n,
        ((Cohomology.Singular.Evaluation.singularScalarChains (R := k) X).homology ij.val.1 ⊗[k]
          (Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y).homology ij.val.2)) :=
  (DirectSum.congrLinearEquiv (fun ij : TensorHomologyD.Construction.TensorHomology.DegreePairs n =>
    (TensorProduct.congr (Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv X ij.val.1)
      (Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv Y ij.val.2)).trans
        (TensorProduct.dualDistribEquiv k
          ((Cohomology.Singular.Evaluation.singularScalarChains (R := k) X).homology ij.val.1)
          ((Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y).homology ij.val.2)))).trans
    (directSumDualEquiv _)

/-- The cohomology decomposition obtained from the proved chain equivalence.
 Its identification with the prescribed cup product is proved separately. -/
def cohomologyKunnethEquiv (n : ℕ) :
    CohomologySum (k := k) X Y n ≃ₗ[k]
      Cohomology.Singular.Basic.singularCohomology (ModuleCat.of k k) (TopCat.of (X × Y)) n :=
  (cohomologySumDualEquiv X Y n).trans
    ((ComparisonLow.Construction.EilenbergZilber.singularHomologyKunneth k X Y n).dualMap.symm.trans
      (Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (TopCat.of (X × Y)) n).symm)

end Construction.CohomologyDecomposition

end

/-! Bidegree projections from the tensor total complex. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.HomologicalComplex
open scoped TensorProduct DirectSum

namespace Construction.TensorProjections

open OAI.AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology

variable {k : Type} [Field k]
variable (C D : ChainComplex (ModuleCat.{0} k) ℕ)

def projection (n : ℕ) (ij : TensorHomologyD.Construction.TensorHomology.DegreePairs n) :
    (C ⊗ D).X n ⟶ C.X ij.val.1 ⊗ D.X ij.val.2 :=
  TensorHomologyD.Construction.TensorHomology.tensorDegreeOut C D n ≫ ModuleCat.ofHom
    (DirectSum.component k (TensorHomologyD.Construction.TensorHomology.DegreePairs n) (fun d => C.X d.val.1 ⊗[k] D.X d.val.2) ij)

@[reassoc (attr := simp)]
theorem inclusion_projection_self (n : ℕ) (ij : TensorHomologyD.Construction.TensorHomology.DegreePairs n) :
    ιTensorObj C D ij.val.1 ij.val.2 n ij.property ≫ projection C D n ij = 𝟙 _ := by
  rw [projection, TensorHomologyD.Construction.TensorHomology.ι_tensorDegreeOut_assoc]
  apply ModuleCat.hom_ext
  exact DirectSum.component_comp_lof_same
    (M := fun d : TensorHomologyD.Construction.TensorHomology.DegreePairs n => C.X d.val.1 ⊗[k] D.X d.val.2) k ij

@[reassoc]
theorem inclusion_projection_ne (n : ℕ) (ij ab : TensorHomologyD.Construction.TensorHomology.DegreePairs n) (h : ab ≠ ij) :
    ιTensorObj C D ab.val.1 ab.val.2 n ab.property ≫ projection C D n ij = 0 := by
  rw [projection, TensorHomologyD.Construction.TensorHomology.ι_tensorDegreeOut_assoc]
  apply ModuleCat.hom_ext
  change (DirectSum.component k (TensorHomologyD.Construction.TensorHomology.DegreePairs n)
    (fun d => C.X d.val.1 ⊗[k] D.X d.val.2) ij).comp
      (DirectSum.lof k (TensorHomologyD.Construction.TensorHomology.DegreePairs n) (fun d => C.X d.val.1 ⊗[k] D.X d.val.2) ab) = 0
  rw [DirectSum.component_comp_lof, dite_eq_right h]

/-- Equality in the tensor total degree can be tested in every bidegree. -/
theorem hom_ext (n : ℕ) {A : ModuleCat.{0} k} (f g : A ⟶ (C ⊗ D).X n)
    (h : ∀ ij, f ≫ projection C D n ij = g ≫ projection C D n ij) : f = g := by
  apply (cancel_mono (TensorHomologyD.Construction.TensorHomology.tensorDegreeIso C D n).inv).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply DFinsupp.ext
  intro ij
  exact ConcreteCategory.congr_hom (h ij) x

abbrev firstDifferential (n : ℕ) : (C ⊗ D).X (n + 1) ⟶ (C ⊗ D).X n :=
  mapBifunctor.D₁ C D (curriedTensor (ModuleCat.{0} k)) (ComplexShape.down ℕ) (n + 1) n

abbrev secondDifferential (n : ℕ) : (C ⊗ D).X (n + 1) ⟶ (C ⊗ D).X n :=
  mapBifunctor.D₂ C D (curriedTensor (ModuleCat.{0} k)) (ComplexShape.down ℕ) (n + 1) n

@[reassoc]
theorem firstDifferential_projection (n p q : ℕ) (hpq : p + q = n) :
    firstDifferential C D n ≫ projection C D n ⟨(p, q), hpq⟩ =
      projection C D (n + 1) ⟨(p + 1, q), by omega⟩ ≫ (C.d (p + 1) p ⊗ₘ 𝟙 (D.X q)) := by
  apply mapBifunctor.hom_ext
  intro i j hij
  change i + j = n + 1 at hij
  change ιMapBifunctor C D (curriedTensor (ModuleCat.{0} k)) (ComplexShape.down ℕ)
    i j (n + 1) hij ≫ mapBifunctor.D₁ C D (curriedTensor (ModuleCat.{0} k))
      (ComplexShape.down ℕ) (n + 1) n ≫ projection C D n ⟨(p, q), hpq⟩ = _
  rw [mapBifunctor.ι_D₁_assoc]
  cases i with
  | zero =>
    rw [mapBifunctor.d₁_eq_zero C D _ _ 0 j n (by simp), zero_comp]
    have hne : (⟨(0, j), hij⟩ : TensorHomologyD.Construction.TensorHomology.DegreePairs (n + 1)) ≠ ⟨(p + 1, q), by omega⟩ := by
      intro h
      have hh := congrArg (fun a : TensorHomologyD.Construction.TensorHomology.DegreePairs (n + 1) => a.val.1) h
      simp at hh
    erw [inclusion_projection_ne_assoc C D (n + 1) _ _ hne, zero_comp]
  | succ i =>
    have hij' : i + j = n := by omega
    rw [mapBifunctor.d₁_eq C D _ _
      (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl) j n hij']
    change ((1 : ℤˣ) • ((C.d (i + 1) i ▷ D.X j) ≫ ιTensorObj C D i j n hij')) ≫ _ = _
    rw [one_smul, Category.assoc]
    by_cases he : (⟨(i, j), hij'⟩ : TensorHomologyD.Construction.TensorHomology.DegreePairs n) = ⟨(p, q), hpq⟩
    · have hi : i = p := congrArg (fun a : TensorHomologyD.Construction.TensorHomology.DegreePairs n => a.val.1) he
      have hj : j = q := congrArg (fun a : TensorHomologyD.Construction.TensorHomology.DegreePairs n => a.val.2) he
      subst p q
      erw [inclusion_projection_self, Category.comp_id,
        inclusion_projection_self_assoc, tensorHom_id]
    · have hne : (⟨(i + 1, j), hij⟩ : TensorHomologyD.Construction.TensorHomology.DegreePairs (n + 1)) ≠
          ⟨(p + 1, q), by omega⟩ := by
        intro h
        apply he
        apply Subtype.ext
        apply Prod.ext
        · exact Nat.succ.inj (congrArg (fun a : TensorHomologyD.Construction.TensorHomology.DegreePairs (n + 1) => a.val.1) h)
        · exact congrArg (fun a : TensorHomologyD.Construction.TensorHomology.DegreePairs (n + 1) => a.val.2) h
      erw [inclusion_projection_ne C D n _ _ he, comp_zero,
        inclusion_projection_ne_assoc C D (n + 1) _ _ hne, zero_comp]

@[reassoc]
theorem secondDifferential_projection (n p q : ℕ) (hpq : p + q = n) :
    secondDifferential C D n ≫ projection C D n ⟨(p, q), hpq⟩ =
      ((-1 : ℤˣ) ^ p) • (projection C D (n + 1) ⟨(p, q + 1), by omega⟩ ≫
        (𝟙 (C.X p) ⊗ₘ D.d (q + 1) q)) := by
  apply mapBifunctor.hom_ext
  intro i j hij
  change i + j = n + 1 at hij
  change ιMapBifunctor C D (curriedTensor (ModuleCat.{0} k)) (ComplexShape.down ℕ)
    i j (n + 1) hij ≫ mapBifunctor.D₂ C D (curriedTensor (ModuleCat.{0} k))
      (ComplexShape.down ℕ) (n + 1) n ≫ projection C D n ⟨(p, q), hpq⟩ = _
  rw [mapBifunctor.ι_D₂_assoc, Linear.comp_units_smul]
  cases j with
  | zero =>
    rw [mapBifunctor.d₂_eq_zero C D _ _ i 0 n (by simp), zero_comp]
    have hne : (⟨(i, 0), hij⟩ : TensorHomologyD.Construction.TensorHomology.DegreePairs (n + 1)) ≠ ⟨(p, q + 1), by omega⟩ := by
      intro h
      have hh := congrArg (fun a : TensorHomologyD.Construction.TensorHomology.DegreePairs (n + 1) => a.val.2) h
      simp at hh
    erw [inclusion_projection_ne_assoc C D (n + 1) _ _ hne, zero_comp, smul_zero]
  | succ j =>
    have hij' : i + j = n := by omega
    rw [mapBifunctor.d₂_eq C D _ _ i
      (show (ComplexShape.down ℕ).Rel (j + 1) j from rfl) n hij']
    change (((-1 : ℤˣ) ^ i) • ((C.X i ◁ D.d (j + 1) j) ≫
      ιTensorObj C D i j n hij')) ≫ _ = _
    rw [Linear.units_smul_comp, Category.assoc]
    by_cases he : (⟨(i, j), hij'⟩ : TensorHomologyD.Construction.TensorHomology.DegreePairs n) = ⟨(p, q), hpq⟩
    · have hi : i = p := congrArg (fun a : TensorHomologyD.Construction.TensorHomology.DegreePairs n => a.val.1) he
      have hj : j = q := congrArg (fun a : TensorHomologyD.Construction.TensorHomology.DegreePairs n => a.val.2) he
      subst p q
      erw [inclusion_projection_self, Category.comp_id,
        inclusion_projection_self_assoc, id_tensorHom]
    · have hne : (⟨(i, j + 1), hij⟩ : TensorHomologyD.Construction.TensorHomology.DegreePairs (n + 1)) ≠
          ⟨(p, q + 1), by omega⟩ := by
        intro h
        apply he
        apply Subtype.ext
        apply Prod.ext
        · exact congrArg (fun a : TensorHomologyD.Construction.TensorHomology.DegreePairs (n + 1) => a.val.1) h
        · exact Nat.succ.inj (congrArg (fun a : TensorHomologyD.Construction.TensorHomology.DegreePairs (n + 1) => a.val.2) h)
      erw [inclusion_projection_ne C D n _ _ he, comp_zero,
        inclusion_projection_ne_assoc C D (n + 1) _ _ hne, zero_comp]
      simp only [smul_zero]

@[reassoc]
theorem differential_projection (n p q : ℕ) (hpq : p + q = n) :
    (C ⊗ D).d (n + 1) n ≫ projection C D n ⟨(p, q), hpq⟩ =
      projection C D (n + 1) ⟨(p + 1, q), by omega⟩ ≫ (C.d (p + 1) p ⊗ₘ 𝟙 (D.X q)) +
      (-1 : ℤ) ^ p • (projection C D (n + 1) ⟨(p, q + 1), by omega⟩ ≫
        (𝟙 (C.X p) ⊗ₘ D.d (q + 1) q)) := by
  change (firstDifferential C D n + secondDifferential C D n) ≫ _ = _
  rw [Preadditive.add_comp, firstDifferential_projection, secondDifferential_projection]
  rfl

/-- Assemble a finite family of maps into the tensor total degree. -/
def lift (n : ℕ) {A : ModuleCat.{0} k}
    (f : ∀ ij : TensorHomologyD.Construction.TensorHomology.DegreePairs n, A ⟶ C.X ij.val.1 ⊗ D.X ij.val.2) :
    A ⟶ (C ⊗ D).X n :=
  ∑ ij, f ij ≫ ιTensorObj C D ij.val.1 ij.val.2 n ij.property

@[reassoc (attr := simp)]
theorem lift_projection (n : ℕ) {A : ModuleCat.{0} k}
    (f : ∀ ij : TensorHomologyD.Construction.TensorHomology.DegreePairs n, A ⟶ C.X ij.val.1 ⊗ D.X ij.val.2)
    (ij : TensorHomologyD.Construction.TensorHomology.DegreePairs n) : lift C D n f ≫ projection C D n ij = f ij := by
  rw [lift, Preadditive.sum_comp]
  rw [Finset.sum_eq_single ij]
  · rw [Category.assoc, inclusion_projection_self, Category.comp_id]
  · intro ab _ hab
    rw [Category.assoc, inclusion_projection_ne C D n ij ab hab, comp_zero]
  · simp

@[reassoc]
theorem inclusion_tensorHom {E F : ChainComplex (ModuleCat.{0} k) ℕ}
    (f : C ⟶ E) (g : D ⟶ F) (n : ℕ) (ij : TensorHomologyD.Construction.TensorHomology.DegreePairs n) :
    ιTensorObj C D ij.val.1 ij.val.2 n ij.property ≫
        (HomologicalComplex.tensorHom f g).f n =
      (f.f ij.val.1 ⊗ₘ g.f ij.val.2) ≫ ιTensorObj E F ij.val.1 ij.val.2 n ij.property := by
  have h := ι_mapBifunctorMap f g (curriedTensor (ModuleCat.{0} k)) (ComplexShape.down ℕ)
    ij.val.1 ij.val.2 n ij.property
  change _ = (f.f ij.val.1 ▷ D.X ij.val.2) ≫
    (E.X ij.val.1 ◁ g.f ij.val.2) ≫ ιTensorObj E F ij.val.1 ij.val.2 n ij.property at h
  exact h.trans ((Category.assoc _ _ _).symm.trans
    (congrArg (fun u => u ≫ ιTensorObj E F ij.val.1 ij.val.2 n ij.property)
      (tensorHom_def (f.f ij.val.1) (g.f ij.val.2)).symm))

@[reassoc]
theorem projection_tensorHom {E F : ChainComplex (ModuleCat.{0} k) ℕ}
    (f : C ⟶ E) (g : D ⟶ F) (n : ℕ) (ij : TensorHomologyD.Construction.TensorHomology.DegreePairs n) :
    (HomologicalComplex.tensorHom f g).f n ≫ projection E F n ij =
      projection C D n ij ≫ (f.f ij.val.1 ⊗ₘ g.f ij.val.2) := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  erw [← Category.assoc, inclusion_tensorHom C D f g n ⟨(p, q), hpq⟩, Category.assoc]
  by_cases h : (⟨(p, q), hpq⟩ : TensorHomologyD.Construction.TensorHomology.DegreePairs n) = ij
  · subst ij
    erw [inclusion_projection_self, Category.comp_id, inclusion_projection_self_assoc]
  · erw [inclusion_projection_ne E F n ij ⟨(p, q), hpq⟩ h, comp_zero,
      inclusion_projection_ne_assoc C D n ij ⟨(p, q), hpq⟩ h, zero_comp]

end Construction.TensorProjections

end

end OAI.AlgebraicTopology.Kunneth.CohomologyTensorNe
