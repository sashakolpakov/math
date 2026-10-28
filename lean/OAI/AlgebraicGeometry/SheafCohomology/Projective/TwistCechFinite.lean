/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechHigher
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeQuotient
import OAI.AlgebraicGeometry.SheafCohomology.Projective.SingletonTwistFiniteness
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteHomologySequence
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechExact
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechPushforward
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation

/-! # Twist Cech Finite -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechFinite.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-!
# Finite homology for finite families of projective twists

This file combines the degree-zero and positive-degree finiteness theorems for a projective twist,
then transfers the result to finite coproducts using additivity of ordered Cech homology.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Ordered base-Cech homology of an integer coordinate-hyperplane twist is finite in every
degree over a Noetherian coefficient ring. -/
theorem coordinateHyperplaneTwist_orderedBaseCechComplex_homology_module_finite_all
    [Fintype σ] [LinearOrder σ] [IsNoetherianRing R]
    (j : σ) (d : ℤ) (q : ℕ) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      ((OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))).homology q) := by
  cases subsingleton_or_nontrivial σ with
  | inl hs =>
      let := hs
      exact SingletonTwistFiniteness.MvPolynomial.coordinateHyperplaneTwist_homology_module_finite_of_subsingleton j d q
  | inr hn =>
      let := hn
      cases q with
      | zero =>
          exact TwistCechHigher.MvPolynomial.coordinateHyperplaneTwist_orderedBaseCechComplex_homology_zero_module_finite j d
      | succ n =>
          exact TwistCechHigher.MvPolynomial.coordinateHyperplaneTwist_orderedBaseCechComplex_homology_module_finite j d n

/-- Ordered base-Cech homology of a finite coproduct of integer coordinate-hyperplane twists is
finite in every degree over a Noetherian coefficient ring. -/
theorem coordinateHyperplaneTwistCoproduct_orderedBaseCechComplex_homology_module_finite
    [Fintype σ] [LinearOrder σ] [IsNoetherianRing R]
    {I : Type} [Finite I] (j : I → σ) (d : I → ℤ) (q : ℕ) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      ((OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (∐ fun i : I ↦ TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) (j i) (d i))
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))).homology q) := by
  classical
  let := Fintype.ofFinite I
  let : HasFiniteBiproducts (Proj (homogeneousSubmodule σ R)).Modules :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let A := Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
  let : HasFiniteBiproducts (ModuleCat.{u} A) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let M : I → (Proj (homogeneousSubmodule σ R)).Modules :=
    fun i ↦ TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) (j i) (d i)
  let F := OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℕ) q
  let : F.Additive := by
    dsimp only [F]
    infer_instance
  let : PreservesFiniteBiproducts F :=
    Functor.preservesFiniteBiproductsOfAdditive F
  let (i : I) : Module.Finite A (F.obj (M i)) :=
    coordinateHyperplaneTwist_orderedBaseCechComplex_homology_module_finite_all
      (R := R) (j i) (d i) q
  let : Module.Finite A (∀ i : I, F.obj (M i)) := Module.Finite.pi
  change Module.Finite A (F.obj (∐ M))
  let e₀ : F.obj (∐ M) ≅ F.obj (⨁ M) :=
    F.mapIso (biproduct.isoCoproduct M).symm
  let e₁ : F.obj (⨁ M) ≅ ⨁ (F.obj ∘ M) := F.mapBiproduct M
  let e₂ : (⨁ (F.obj ∘ M)) ≅ ∏ᶜ (F.obj ∘ M) :=
    biproduct.isoProduct (F.obj ∘ M)
  let e₃ : (∏ᶜ (F.obj ∘ M)) ≅ ModuleCat.of A (∀ i : I, F.obj (M i)) :=
    ModuleCat.piIsoPi (F.obj ∘ M)
  exact Module.Finite.equiv
    ((e₀ ≪≫ e₁ ≪≫ e₂ ≪≫ e₃).symm.toLinearEquiv)

/-- Ordered base-Cech homology of a finite coproduct of nonnegative powers of coordinate
hyperplane ideal modules is finite in every degree over a Noetherian coefficient ring. -/
theorem coordinateHyperplaneIdealModulePowerCoproduct_orderedBaseCechComplex_homology_module_finite
    [Fintype σ] [LinearOrder σ] [IsNoetherianRing R]
    {I : Type} [Finite I] (j : I → σ) (n : I → ℕ) (q : ℕ) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      ((OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (∐ fun i : I ↦ TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (j i) (n i))
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))).homology q) := by
  let d : I → ℤ := fun i ↦
    match n i with
    | 0 => 0
    | k + 1 => .negSucc k
  have hd (i : I) :
      TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) (j i) (d i) =
        TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (j i) (n i) := by
    rcases hn : n i with _ | k
    · simp [d, hn, TwistPowers.MvPolynomial.coordinateHyperplaneTwist]
    · simp [d, hn, TwistPowers.MvPolynomial.coordinateHyperplaneTwist]
  have hfamily :
      (fun i : I ↦ TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) (j i) (d i)) =
        fun i : I ↦ TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (j i) (n i) :=
    funext hd
  rw [← hfamily]
  exact coordinateHyperplaneTwistCoproduct_orderedBaseCechComplex_homology_module_finite
    (R := R) j d q

private theorem orderedBaseCechComplex_homology_module_finite_of_card_le
    [Fintype σ] [LinearOrder σ] [IsNoetherianRing R]
    (M : (Proj (homogeneousSubmodule σ R)).Modules) (q : ℕ)
    (hq : Fintype.card (ULift.{u} σ) ≤ q) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      ((OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) M
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))).homology q) := by
  let C := OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
    (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) M
    (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
  have hX : IsZero (C.X q) := by
    dsimp only [C, OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex]
    exact OrderedBaseCech.Scheme.Modules.orderedBaseCechObject_isZero_of_card_le
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) M
      (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) q hq
  have hH : IsZero (C.homology q) :=
    ShortComplex.isZero_homology_of_isZero_X₂ (C.sc q) hX
  let : Subsingleton (C.homology q) := ModuleCat.subsingleton_of_isZero hH
  change Module.Finite
    Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
    (C.homology q)
  infer_instance

private theorem finiteType_orderedBaseCechComplex_homology_module_finite_of_card_le_add
    [Fintype σ] [LinearOrder σ] [IsNoetherianRing R]
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (q n : ℕ)
    (hcard : Fintype.card (ULift.{u} σ) ≤ q + n) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      ((OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) M
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))).homology q) := by
  let : IsNoetherianRing
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens)) :=
    isNoetherianRing_of_ringEquiv R
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  induction n generalizing M q with
  | zero =>
      exact orderedBaseCechComplex_homology_module_finite_of_card_le M q (by
        simpa using hcard)
  | succ n ih =>
      by_cases hq : Fintype.card (ULift.{u} σ) ≤ q
      · exact orderedBaseCechComplex_homology_module_finite_of_card_le M q hq
      · obtain ⟨r, j, d, f, hf⟩ := NegativeQuotient.MvPolynomial.exists_fin_coordinateNegativeTwist_quotient M
        let L : Fin r → (Proj (homogeneousSubmodule σ R)).Modules := fun i ↦
          TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (j i) (d i)
        let Q : (Proj (homogeneousSubmodule σ R)).Modules := ∐ L
        let : Epi f := hf
        let : Q.IsQuasicoherent := by
          dsimp only [Q]
          apply Quasicoherent.Scheme.Modules.isQuasicoherent_coproduct
          intro i
          exact InvertibleFinitePresentation.invertible_quasicoherent
            (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible
              (R := R) (j i) (d i))
        let : Q.IsFiniteType := by
          dsimp only [Q]
          apply Quasicoherent.Scheme.Modules.isFiniteType_fin_coproduct L
          · intro i
            exact InvertibleFinitePresentation.invertible_quasicoherent
              (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible
                (R := R) (j i) (d i))
          · intro i
            let : (L i).IsFinitePresentation :=
              InvertibleFinitePresentation.invertible_finitePresentation
                (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible
                  (R := R) (j i) (d i))
            refine { exists_localGeneratorsData := ?_ }
            obtain ⟨p, hp⟩ :=
              SheafOfModules.IsFinitePresentation.exists_quasicoherentData (L i)
            refine ⟨p.localGeneratorsData, ?_⟩
            constructor
            intro k
            exact (hp.isFinite_presentation k).isFiniteType_generators
        let : LocallyOfFiniteType
            (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) :=
          MvPolynomialClosure.MvPolynomial.homogeneousProjπ_locallyOfFiniteType (R := R) (σ := σ)
        let : IsLocallyNoetherian (Proj (homogeneousSubmodule σ R)) :=
          LocallyOfFiniteType.isLocallyNoetherian
            (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        let : (kernel f).IsQuasicoherent :=
          Quasicoherent.Scheme.Modules.isQuasicoherent_kernel f
        let : (kernel f).IsFiniteType :=
          Quasicoherent.Scheme.Modules.isFiniteType_kernel f
        have hcard' : Fintype.card (ULift.{u} σ) ≤ (q + 1) + n := by
          omega
        let : Module.Finite
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            ((OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
              (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (kernel f)
              (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))).homology (q + 1)) :=
          ih (kernel f) (q + 1) hcard'
        let : Module.Finite
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            ((OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
              (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) Q
              (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))).homology q) := by
          dsimp only [Q, L]
          exact
            coordinateHyperplaneIdealModulePowerCoproduct_orderedBaseCechComplex_homology_module_finite
              (R := R) j d q
        let T := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
        have hT : T.ShortExact := { exact := ShortComplex.kernelSequence_exact f }
        have hTC := OrderedBaseCechExact.CategoryTheory.ShortComplex.ShortExact.map_orderedBaseCechComplexFunctor_of_affine_openCover
          (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
          (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
          (StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R))
          hT
        let F := OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor
          (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
          (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
        let : Module.Finite
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            ((T.map F).X₂.homology q) := by
          change Module.Finite
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            ((OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
              (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) Q
              (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))).homology q)
          infer_instance
        let : Module.Finite
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            ((T.map F).X₁.homology (q + 1)) := by
          change Module.Finite
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            ((OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
              (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (kernel f)
              (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))).homology (q + 1))
          infer_instance
        change Module.Finite
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          ((T.map F).X₃.homology q)
        exact FiniteHomologySequence.CategoryTheory.ShortComplex.ShortExact.finite_homology_X3
          hTC q (q + 1) (by simp [ComplexShape.up_Rel])

/-- Ordered base-Cech homology of a finite-type quasicoherent module on polynomial projective
space is finite in every degree over a Noetherian coefficient ring. -/
theorem finiteType_orderedBaseCechComplex_homology_module_finite
    [Fintype σ] [LinearOrder σ] [IsNoetherianRing R]
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (q : ℕ) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      ((OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) M
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))).homology q) := by
  exact finiteType_orderedBaseCechComplex_homology_module_finite_of_card_le_add
    M q (Fintype.card (ULift.{u} σ)) (by omega)

/-- Ordered base-Cech homology of a finite-type quasicoherent module on a closed subscheme of
polynomial projective space is finite in every degree over a Noetherian coefficient ring. -/
theorem closedImmersion_finiteType_orderedBaseCechComplex_homology_module_finite
    [Fintype σ] [LinearOrder σ] [IsNoetherianRing R]
    {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (q : ℕ) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      ((OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
        (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) M
        (fun j => f ⁻¹ᵁ StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ) j)).homology q) := by
  let N := (AlgebraicGeometry.Scheme.Modules.pushforward f).obj M
  let : N.IsQuasicoherent :=
    Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f
  let : N.IsFiniteType :=
    Quasicoherent.Scheme.Modules.isFiniteType_pushforward_of_isClosedImmersion f
  let : Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      ((OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) N
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))).homology q) :=
    finiteType_orderedBaseCechComplex_homology_module_finite N q
  exact Module.Finite.equiv
    (HomologicalComplex.homologyMapIso
      (OrderedBaseCechPushforward.Scheme.Modules.orderedBaseCechComplexPushforwardIso f
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) M
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))) q).symm.toLinearEquiv

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechFinite.MvPolynomial
