import OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentPolynomialAction

/-! # Laurent Cech Polynomial Action -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentCechPolynomialAction

noncomputable section

/-! Polynomial multiplication is a chain map on the original homogeneous
Laurent presentation of the projective ordered Čech complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentPolynomialAction

universe u

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev Factor (d : ℤ) {n : ℕ} (a : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :=
  ModuleCat.of Γ(Spec (CommRingCat.of R), ⊤)
    (AddMonoidAlgebra Γ(Spec (CommRingCat.of R), ⊤) (LaurentPolynomialAction.Allowed d (fun k => (a.1 k).down)))

def objectMap (m : ℕ) (d : ℤ)
    (P : homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) m) (n : ℕ) :
    AlgebraicGeometry.SheafCohomology.Projective.LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n ⟶
      AlgebraicGeometry.SheafCohomology.Projective.LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) ((m : ℤ) + d) n :=
  Limits.Pi.map fun a : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
    ModuleCat.ofHom (LaurentPolynomialAction.polynomial Γ(Spec (CommRingCat.of R), ⊤) m d (fun k => (a.1 k).down) P)

@[reassoc]
theorem objectMap_π (m : ℕ) (d : ℤ)
    (P : homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) m) (n : ℕ)
    (a : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :
    objectMap (R := R) m d P n ≫ Pi.π (Factor (R := R) ((m : ℤ) + d)) a =
      Pi.π (Factor (R := R) d) a ≫
        ModuleCat.ofHom (LaurentPolynomialAction.polynomial Γ(Spec (CommRingCat.of R), ⊤) m d
          (fun k => (a.1 k).down) P) :=
  Pi.map_π _ a

omit [Fintype σ] in
theorem deletion_range {n : ℕ}
    (a : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (k : Fin (n + 2)) :
    Set.range (fun l => ((a.delete k).1 l).down) ⊆ Set.range (fun l => (a.1 l).down) := by
  rintro i ⟨l, rfl⟩
  exact ⟨k.succAbove l, rfl⟩

theorem factor_commutes (m : ℕ) (d : ℤ)
    (P : homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) m) {n : ℕ}
    (a : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (k : Fin (n + 2)) :
    ModuleCat.ofHom (LaurentPolynomialAction.polynomial Γ(Spec (CommRingCat.of R), ⊤) m d
        (fun l => ((a.delete k).1 l).down) P) ≫
      ModuleCat.ofHom (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateHomogeneousLaurentDeleteLinearMap
        (R := R) a k ((m : ℤ) + d)) =
    ModuleCat.ofHom (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateHomogeneousLaurentDeleteLinearMap (R := R) a k d) ≫
      ModuleCat.ofHom (LaurentPolynomialAction.polynomial Γ(Spec (CommRingCat.of R), ⊤) m d
        (fun l => (a.1 l).down) P) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact LaurentPolynomialAction.polynomial_restriction Γ(Spec (CommRingCat.of R), ⊤) m d
    (fun l => ((a.delete k).1 l).down) (fun l => (a.1 l).down) (deletion_range a k) P x

theorem coface_commutes (m : ℕ) (d : ℤ)
    (P : homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) m) (n : ℕ) (k : Fin (n + 2)) :
    objectMap (R := R) m d P n ≫
      AlgebraicGeometry.SheafCohomology.Projective.LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechCoface (R := R) (σ := σ) ((m : ℤ) + d) n k =
    AlgebraicGeometry.SheafCohomology.Projective.LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechCoface (R := R) (σ := σ) d n k ≫
      objectMap (R := R) m d P (n + 1) := by
  apply Pi.hom_ext
  intro a
  unfold objectMap AlgebraicGeometry.SheafCohomology.Projective.LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechCoface
  erw [Category.assoc, Pi.lift_comp_π, Pi.map_π_assoc,
    Category.assoc, Pi.map_π, Pi.lift_comp_π_assoc]
  rw [factor_commutes]
  exact (Category.assoc _ _ _).symm

theorem differential_commutes (m : ℕ) (d : ℤ)
    (P : homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) m) (n : ℕ) :
    objectMap (R := R) m d P n ≫
      AlgebraicGeometry.SheafCohomology.Projective.LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential (R := R) (σ := σ) ((m : ℤ) + d) n =
    AlgebraicGeometry.SheafCohomology.Projective.LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential (R := R) (σ := σ) d n ≫
      objectMap (R := R) m d P (n + 1) := by
  simp only [AlgebraicGeometry.SheafCohomology.Projective.LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential,
    Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp, coface_commutes]

def chainMap (j : σ) (m : ℕ) (d : ℤ)
    (P : homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) m) :
    AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d ⟶
      AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j ((m : ℤ) + d) where
  f := objectMap (R := R) m d P
  comm' n k h := by
    have hk : n + 1 = k := h
    subst k
    simpa only [AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex_d,
      AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex_X] using
      differential_commutes (R := R) m d P n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentCechPolynomialAction
