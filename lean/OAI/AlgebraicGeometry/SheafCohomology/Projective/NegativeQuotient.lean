/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMaps
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleEpiCover
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent

/-! # Negative Quotient -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeQuotient.MvPolynomial

noncomputable section

open _root_.MvPolynomial

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem moduleSectionsOfTop_eval_top
    {X : Scheme.{u}} (M : X.Modules) (s : M.sections) :
    AffineRankOne.globalSectionFamily M (s.eval (Opposite.op ⊤)) = s := by
  apply PresheafOfModules.sections_ext
  intro V
  change M.val.map (homOfLE (le_top : V.unop ≤ (⊤ : X.Opens))).op
      (s.val (Opposite.op ⊤)) = s.val V
  exact s.property _

private theorem sectionsMap_moduleSectionsOfTop
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (x : Γ(M, (⊤ : X.Opens))) :
    SheafOfModules.sectionsMap f (AffineRankOne.globalSectionFamily M x) =
      AffineRankOne.globalSectionFamily N (f.val.app (Opposite.op ⊤) x) := by
  apply PresheafOfModules.sections_ext
  intro V
  let i := (homOfLE (le_top : V.unop ≤ (⊤ : X.Opens))).op
  change f.val.app V (M.val.map i x) =
    N.val.map i (f.val.app (Opposite.op ⊤) x)
  exact ConcreteCategory.congr_hom (f.val.naturality i) x

/-- Every finite-type quasicoherent module on polynomial projective space is a
finite quotient of powers of coordinate-hyperplane ideal modules. -/
theorem exists_finite_coordinateNegativeTwist_quotient [Fintype σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ (I : Type u) (_ : Finite I) (j : I → σ) (n : I → ℕ)
        (f : (∐ fun i : I ↦
          TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (j i) (n i)) ⟶ M),
      Epi f := by
  classical
  let X := Proj (homogeneousSubmodule σ R)
  let U : σ → X.Opens := fun j ↦ MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j
  have hgenerators (j : σ) :
      ∃ G : ((Scheme.Modules.restrictFunctor (U j).ι).obj M).GeneratingSections,
        G.IsFiniteType := by
    exact
      Quasicoherent.Scheme.Modules.exists_generatingSections_restrict_of_isFiniteType_of_isAffineOpen
        M ⟨U j, MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen (R := R) j⟩
  choose G hG using hgenerators
  let generatorsFiniteType (j : σ) : (G j).IsFiniteType := hG j
  let generatorIndexFinite (j : σ) : Finite (G j).I := (hG j).finite
  let chartSection (j : σ) (a : (G j).I) : Γ(M, U j) :=
    (M.presheaf.mapIso (eqToIso (U j).ι_image_top).op).inv
      ((M.restrictAppIso (U j).ι ⊤).hom
        (((G j).s a).eval (Opposite.op ⊤)))
  have hnegative (j : σ) (a : (G j).I) :=
    NegativeTwistMaps.MvPolynomial.exists_coordinateNegativeTwistHom_frameSection_eq M j (chartSection j a)
  choose n f hf using hnegative
  let I := Σ j : σ, (G j).I
  let ji : I → σ := fun i ↦ i.1
  let ni : I → ℕ := fun i ↦ n i.1 i.2
  let L : I → X.Modules := fun i ↦
    TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (ji i) (ni i)
  let p : ∀ i : I, L i ⟶ M := fun i ↦ f i.1 i.2
  let q : (∐ L) ⟶ M := Limits.Sigma.desc p
  let restrictedSummandFrame (j : σ) (a : (G j).I) :
      Γ((Scheme.Modules.restrictFunctor (U j).ι).obj (L ⟨j, a⟩), ⊤) :=
    (((L ⟨j, a⟩).restrictAppIso (U j).ι ⊤).inv)
      (((L ⟨j, a⟩).presheaf.mapIso
        (eqToIso (U j).ι_image_top).op).hom
          (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerFrameSection
            (R := R) j j (n j a)))
  let restrictedFrame (j : σ) (a : (G j).I) :
      Γ((Scheme.Modules.restrictFunctor (U j).ι).obj (∐ L), ⊤) :=
    ((Scheme.Modules.restrictFunctor (U j).ι).map
      (Limits.Sigma.ι L ⟨j, a⟩)).val.app (Opposite.op ⊤)
        (restrictedSummandFrame j a)
  have hrestrictedFrame (j : σ) (a : (G j).I) :
      ((Scheme.Modules.restrictFunctor (U j).ι).map q).val.app
          (Opposite.op ⊤) (restrictedFrame j a) =
        ((G j).s a).eval (Opposite.op ⊤) := by
    have hmor :
        (Scheme.Modules.restrictFunctor (U j).ι).map
              (Limits.Sigma.ι L ⟨j, a⟩) ≫
            (Scheme.Modules.restrictFunctor (U j).ι).map q =
          (Scheme.Modules.restrictFunctor (U j).ι).map (f j a) := by
      rw [← (Scheme.Modules.restrictFunctor (U j).ι).map_comp]
      change (Scheme.Modules.restrictFunctor (U j).ι).map
        (Limits.Sigma.ι L ⟨j, a⟩ ≫ Limits.Sigma.desc p) = _
      rw [Limits.Sigma.ι_comp_desc]
    have happ := congrArg
      (fun r ↦ r.val.app (Opposite.op ⊤) (restrictedSummandFrame j a)) hmor
    change ((Scheme.Modules.restrictFunctor (U j).ι).map q).val.app
        (Opposite.op ⊤) (restrictedFrame j a) =
      ((Scheme.Modules.restrictFunctor (U j).ι).map (f j a)).val.app
        (Opposite.op ⊤) (restrictedSummandFrame j a) at happ
    rw [happ]
    change (f j a).val.app
        ((U j).ι.opensFunctor.op.obj (Opposite.op ⊤))
          (restrictedSummandFrame j a) = _
    change (f j a).val.app
      (Opposite.op ((U j).ι ''ᵁ (⊤ : (U j).toScheme.Opens)))
        (restrictedSummandFrame j a) = _
    change (f j a).val.app
        (Opposite.op ((U j).ι ''ᵁ (⊤ : (U j).toScheme.Opens)))
          (((TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower
              (R := R) j (n j a)).presheaf.mapIso
            (eqToIso (U j).ι_image_top).op).hom
              (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerFrameSection
                (R := R) j j (n j a))) =
      ((M.restrictAppIso (U j).ι ⊤).hom
        (((G j).s a).eval (Opposite.op ⊤)))
    have hnat := PresheafOfModules.naturality_apply (f j a).val
      (eqToIso (U j).ι_image_top).op.hom
      (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerFrameSection
        (R := R) j j (n j a))
    change (f j a).val.app
        (Opposite.op ((U j).ι ''ᵁ (⊤ : (U j).toScheme.Opens)))
          (((TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower
              (R := R) j (n j a)).presheaf.mapIso
            (eqToIso (U j).ι_image_top).op).hom
              (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerFrameSection
                (R := R) j j (n j a))) =
      (M.presheaf.mapIso (eqToIso (U j).ι_image_top).op).hom
        ((f j a).val.app (Opposite.op (U j))
          (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerFrameSection
            (R := R) j j (n j a))) at hnat
    rw [hnat, hf j a]
    simp only [chartSection, Iso.inv_hom_id_apply]
    rfl
  let localFrame (j : σ) (a : (G j).I) :
      ((Scheme.Modules.restrictFunctor (U j).ι).obj (∐ L)).sections :=
    AffineRankOne.globalSectionFamily _ (restrictedFrame j a)
  let lift (j : σ) :
      SheafOfModules.free (G j).I ⟶
        (Scheme.Modules.restrictFunctor (U j).ι).obj (∐ L) :=
    (((Scheme.Modules.restrictFunctor (U j).ι).obj (∐ L)).freeHomEquiv).symm
      (localFrame j)
  have hlift (j : σ) :
      lift j ≫ (Scheme.Modules.restrictFunctor (U j).ι).map q = (G j).π := by
    have hlocal :
        (fun a ↦ SheafOfModules.sectionsMap
          ((Scheme.Modules.restrictFunctor (U j).ι).map q) (localFrame j a)) =
          (G j).s := by
      funext a
      change SheafOfModules.sectionsMap
          ((Scheme.Modules.restrictFunctor (U j).ι).map q)
            (AffineRankOne.globalSectionFamily _ (restrictedFrame j a)) =
        (G j).s a
      rw [sectionsMap_moduleSectionsOfTop]
      rw [hrestrictedFrame]
      exact moduleSectionsOfTop_eval_top _ _
    change
      (((Scheme.Modules.restrictFunctor (U j).ι).obj (∐ L)).freeHomEquiv).symm
          (localFrame j) ≫
        (Scheme.Modules.restrictFunctor (U j).ι).map q =
      (((Scheme.Modules.restrictFunctor (U j).ι).obj M).freeHomEquiv).symm
        ((G j).s)
    calc
      _ = (((Scheme.Modules.restrictFunctor (U j).ι).obj M).freeHomEquiv).symm
          (fun a ↦ SheafOfModules.sectionsMap
            ((Scheme.Modules.restrictFunctor (U j).ι).map q) (localFrame j a)) :=
        SheafOfModules.freeHomEquiv_symm_comp (localFrame j)
          ((Scheme.Modules.restrictFunctor (U j).ι).map q)
      _ = _ := congrArg
        (((Scheme.Modules.restrictFunctor (U j).ι).obj M).freeHomEquiv).symm hlocal
  have hrestrictedEpi (j : σ) :
      Epi ((Scheme.Modules.restrictFunctor (U j).ι).map q) := by
    constructor
    intro Z g h hgh
    apply (G j).epi.left_cancellation g h
    have hpre := congrArg
      (fun k : (Scheme.Modules.restrictFunctor (U j).ι).obj (∐ L) ⟶ Z ↦
        lift j ≫ k) hgh
    have hcomp :
        (lift j ≫ (Scheme.Modules.restrictFunctor (U j).ι).map q) ≫ g =
          (lift j ≫ (Scheme.Modules.restrictFunctor (U j).ι).map q) ≫ h := by
      exact (Category.assoc _ _ _).trans
        (hpre.trans (Category.assoc _ _ _).symm)
    have hleft := congrArg (fun k ↦ k ≫ g) (hlift j)
    have hright := congrArg (fun k ↦ k ≫ h) (hlift j)
    exact hleft.symm.trans (hcomp.trans hright)
  have hU : ⨆ j, U j = ⊤ := by
    simpa only [U] using MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top (R := R) (σ := σ)
  have hq : Epi q :=
    ModuleEpiCover.Scheme.Modules.epi_of_restrictFunctor_map_epi_of_iSup_eq_top
      U hU q hrestrictedEpi
  let : Finite I := inferInstance
  exact ⟨I, inferInstance, ji, ni, q, hq⟩

/-- Every finite-type quasicoherent module on polynomial projective space is a quotient of a
`Fin`-indexed finite coproduct of powers of coordinate-hyperplane ideal modules. -/
theorem exists_fin_coordinateNegativeTwist_quotient [Fintype σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ (r : ℕ) (j : Fin r → σ) (n : Fin r → ℕ)
        (f : (∐ fun i : Fin r ↦
          TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (j i) (n i)) ⟶ M),
      Epi f := by
  classical
  obtain ⟨I, hI, j, n, f, hf⟩ :=
    exists_finite_coordinateNegativeTwist_quotient M
  let : Finite I := hI
  let e : Fin (Nat.card I) ≃ I := (Finite.equivFin I).symm
  let L : I → (Proj (homogeneousSubmodule σ R)).Modules := fun i ↦
    TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (j i) (n i)
  let g : (∐ fun k : Fin (Nat.card I) ↦ L (e k)) ⟶ M :=
    (Sigma.reindex e L).hom ≫ f
  refine ⟨Nat.card I, fun k ↦ j (e k), fun k ↦ n (e k), g, ?_⟩
  dsimp only [g]
  infer_instance

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeQuotient.MvPolynomial
