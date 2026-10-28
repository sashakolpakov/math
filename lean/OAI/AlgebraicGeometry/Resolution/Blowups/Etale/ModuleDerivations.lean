import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.TransverseHypersurfaceCoordinates
import Mathlib.Algebra.MvPolynomial.Derivation

/-! # Module Derivations -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ModuleDerivations.Construction

noncomputable section

section

/-! The coordinate basis of derivations relative to the coefficient
field on an actual étale polynomial chart. -/

variable {σ K S : Type*} [Field K] [CommRing S]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]
  [Algebra K S] [IsScalarTower K (MvPolynomial σ K) S]

/-- A derivation relative to the coefficient field is determined by
its values on the étale coordinate functions. -/
theorem etale_relative_derivation_ext (D E : Derivation K S S)
    (h : ∀ i : σ, D (algebraMap (MvPolynomial σ K) S (MvPolynomial.X i)) =
      E (algebraMap (MvPolynomial σ K) S (MvPolynomial.X i))) : D = E := by
  have he : D.compAlgebraMap (MvPolynomial σ K) = E.compAlgebraMap (MvPolynomial σ K) :=
    MvPolynomial.derivation_ext h
  apply Blowups.Etale.Derivation.Construction.etaleDerivation_ext (R := MvPolynomial σ K)
  intro p
  exact Derivation.congr_fun he p

variable [Fintype σ] [DecidableEq σ]

/-- Every relative derivation is exactly the linear combination of the
coordinate partial derivatives given by its coordinate values. -/
theorem etale_relative_derivation_eq_sum (D : Derivation K S S) :
    D = ∑ i : σ, D (algebraMap (MvPolynomial σ K) S (MvPolynomial.X i)) •
      DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := S) i := by
  apply etale_relative_derivation_ext (σ := σ)
  intro j
  have hsum := congrArg
    (fun g : S → S => g (algebraMap (MvPolynomial σ K) S (MvPolynomial.X j)))
    (map_sum (Derivation.coeFnAddMonoidHom : Derivation K S S →+ S → S)
      (fun i : σ => D (algebraMap (MvPolynomial σ K) S (MvPolynomial.X i)) •
        DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := S) i) Finset.univ)
  simp only [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply,
    Derivation.smul_apply, smul_eq_mul, TransverseHypersurfaceCoordinates.Construction.etaleRelativePartial_X] at hsum
  rw [hsum]
  simp

/-- The same basis formula evaluated on any section, for use in
coordinate-independent differential ideal comparisons. -/
theorem etale_relative_derivation_apply (D : Derivation K S S) (p : S) :
    D p = ∑ i : σ, D (algebraMap (MvPolynomial σ K) S (MvPolynomial.X i)) *
      DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := S) i p := by
  have he := Derivation.congr_fun (etale_relative_derivation_eq_sum (σ := σ) D) p
  have hsum := congrArg (fun g : S → S => g p)
    (map_sum (Derivation.coeFnAddMonoidHom : Derivation K S S →+ S → S)
      (fun i : σ => D (algebraMap (MvPolynomial σ K) S (MvPolynomial.X i)) •
        DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := S) i) Finset.univ)
  exact he.trans (by simpa only [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply,
    Derivation.smul_apply, smul_eq_mul] using hsum)

end

/-! Étale coordinate expansion for derivations with values in arbitrary modules. -/

variable {k A B M : Type*} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
  [Algebra.FormallyEtale A B] [AddCommGroup M] [Module B M] [Module k M]
  [IsScalarTower k B M] [Module A M] [IsScalarTower A B M] [IsScalarTower k A M]

/-- Étale uniqueness of module-valued derivations, including universal
Kähler derivations. -/
theorem etaleModuleDerivation_ext (D E : Derivation k B M)
    (h : ∀ a : A, D (algebraMap A B a) = E (algebraMap A B a)) : D = E := by
  have hlin : D.liftKaehlerDifferential = E.liftKaehlerDifferential := by
    apply (KaehlerDifferential.isBaseChange_of_formallyEtale k A B).algHom_ext'
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    intro a
    change D.liftKaehlerDifferential
        (KaehlerDifferential.map k k A B (KaehlerDifferential.D k A a)) =
      E.liftKaehlerDifferential
        (KaehlerDifferential.map k k A B (KaehlerDifferential.D k A a))
    rw [KaehlerDifferential.map_D, Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D]
    exact h a
  apply Derivation.ext
  intro b
  rw [← Derivation.liftKaehlerDifferential_comp_D D b,
    ← Derivation.liftKaehlerDifferential_comp_D E b, hlin]

variable {σ K R N : Type*} [Field K] [CommRing R] [AddCommGroup N]
  [Algebra (MvPolynomial σ K) R] [Algebra.Etale (MvPolynomial σ K) R]
  [Algebra K R] [IsScalarTower K (MvPolynomial σ K) R]
  [Module R N] [Module K N] [IsScalarTower K R N]

theorem etale_coordinate_module_derivation_ext (D E : Derivation K R N)
    (h : ∀ i : σ, D (algebraMap (MvPolynomial σ K) R (MvPolynomial.X i)) =
      E (algebraMap (MvPolynomial σ K) R (MvPolynomial.X i))) : D = E := by
  let : Module (MvPolynomial σ K) N := Module.compHom N (algebraMap (MvPolynomial σ K) R)
  let : IsScalarTower (MvPolynomial σ K) R N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower K (MvPolynomial σ K) N :=
    IsScalarTower.of_algebraMap_smul (by
      intro a x
      change algebraMap (MvPolynomial σ K) R (algebraMap K (MvPolynomial σ K) a) • x = a • x
      rw [← IsScalarTower.algebraMap_apply K (MvPolynomial σ K) R]
      exact IsScalarTower.algebraMap_smul R a x)
  have he : D.compAlgebraMap (MvPolynomial σ K) = E.compAlgebraMap (MvPolynomial σ K) :=
    MvPolynomial.derivation_ext h
  apply etaleModuleDerivation_ext (A := MvPolynomial σ K)
  intro p
  exact Derivation.congr_fun he p

variable [Fintype σ] [DecidableEq σ]

/-- The coordinate chain rule with values in an arbitrary module. -/
theorem etale_coordinate_module_derivation_expansion (D : Derivation K R N) (x : R) :
    D x = ∑ i : σ, DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := R) i x •
      D (algebraMap (MvPolynomial σ K) R (MvPolynomial.X i)) := by
  let E : σ → Derivation K R N := fun i =>
    (LinearMap.toSpanSingleton R N
      (D (algebraMap (MvPolynomial σ K) R (MvPolynomial.X i)))).compDer
        (DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := R) i)
  have he : D = ∑ i : σ, E i := by
    apply etale_coordinate_module_derivation_ext (σ := σ)
    intro j
    have hsum := congrArg
      (fun f : R → N => f (algebraMap (MvPolynomial σ K) R (MvPolynomial.X j)))
      (map_sum (Derivation.coeFnAddMonoidHom : Derivation K R N →+ R → N) E Finset.univ)
    simp only [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply] at hsum
    rw [hsum]
    change D (algebraMap (MvPolynomial σ K) R (MvPolynomial.X j)) =
      ∑ i : σ, DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := R) i
        (algebraMap (MvPolynomial σ K) R (MvPolynomial.X j)) •
          D (algebraMap (MvPolynomial σ K) R (MvPolynomial.X i))
    simp [TransverseHypersurfaceCoordinates.Construction.etaleRelativePartial_X]
  have hsum := congrArg (fun f : R → N => f x)
    (map_sum (Derivation.coeFnAddMonoidHom : Derivation K R N →+ R → N) E Finset.univ)
  calc
    D x = (∑ i : σ, E i) x := Derivation.congr_fun he x
    _ = ∑ i : σ, E i x := by
      simpa only [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply] using hsum
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ModuleDerivations.Construction
