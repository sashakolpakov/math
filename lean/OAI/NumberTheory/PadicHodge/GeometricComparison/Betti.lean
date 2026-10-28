import OAI.AlgebraicGeometry.Comparison.Betti.Target
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.AdapterNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.BettiFinite

/-! # Betti -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison

/-! The full BettiComparison input and its comparison on GeometricComparison's actual complex de Rham object. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def Betti.ComparisonInput : Prop := AlgebraicGeometry.Comparison.Betti.Target.ComparisonTarget

namespace Betti.ComplexComparison

def equivOfBijective {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℂ M] [Module ℂ N] (f : M →ₗ[ℂ] N) (hf : Function.Bijective f) : M ≃ₗ[ℂ] N :=
  LinearEquiv.ofBijective f hf

theorem equivOfBijective_toLinearMap {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℂ M] [Module ℂ N] (f : M →ₗ[ℂ] N) (hf : Function.Bijective f) :
    (equivOfBijective f hf).toLinearMap = f := rfl

variable (hBettiComparison : ComparisonInput) (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
  [Smooth X.hom] [IsProper X.hom]

def originalEquiv (n : ℕ) : AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRham X n ≃ₗ[ℂ]
    AlgebraicGeometry.Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) X n := by
  letI := hBettiComparison.1 X n
  exact equivOfBijective (AlgebraicGeometry.Comparison.Betti.Target.smoothDeRhamBettiLinearMap X n)
    ((AlgebraicGeometry.Comparison.Betti.Smooth.ReferenceCongruence.bettiDownEquiv X n).bijective.comp
      ((asIso (AlgebraicGeometry.Comparison.Betti.Smooth.ReferenceCongruence.smoothDeRhamBettiMap X n)).toLinearEquiv.bijective))

theorem originalEquiv_toLinearMap (n : ℕ) :
    (originalEquiv hBettiComparison X n).toLinearMap = AlgebraicGeometry.Comparison.Betti.Target.smoothDeRhamBettiLinearMap X n :=
  equivOfBijective_toLinearMap _ _

def nativeEquiv (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℂ X n ≃ₗ[ℂ]
    AlgebraicGeometry.Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) X n :=
  (SheafFormsAdapter.FormsAdapter.cohomologyEquiv X n).symm.trans (originalEquiv hBettiComparison X n)

theorem inverse_trans_comp {M N T : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup T] [Module ℂ M] [Module ℂ N] [Module ℂ T]
    (e : M ≃ₗ[ℂ] N) (d : M ≃ₗ[ℂ] T) :
    (e.symm.trans d).toLinearMap.comp e.toLinearMap = d.toLinearMap := by
  apply LinearMap.ext
  intro x
  exact congrArg d (e.symm_apply_apply x)

theorem nativeEquiv_comp_forms (n : ℕ) :
    (nativeEquiv hBettiComparison X n).toLinearMap.comp (SheafFormsAdapter.FormsAdapter.cohomologyEquiv X n).toLinearMap =
      AlgebraicGeometry.Comparison.Betti.Target.smoothDeRhamBettiLinearMap X n :=
  (inverse_trans_comp (SheafFormsAdapter.FormsAdapter.cohomologyEquiv X n) (originalEquiv hBettiComparison X n)).trans
    (originalEquiv_toLinearMap hBettiComparison X n)

theorem nativeEquiv_filtration (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom) (n : ℕ) (r : ℤ) :
    (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℂ X n r).map (nativeEquiv hBettiComparison X n).toLinearMap =
      AlgebraicGeometry.Comparison.Betti.Target.projectiveBettiHodgeFiltration (AlgebraicGeometry.Comparison.Betti.Target.projectivePresentation X P) n r := by
  have h₁ := congrArg (Submodule.map (nativeEquiv hBettiComparison X n).toLinearMap)
    (FilteredComplexAdapter.FormsAdapter.cohomologyEquiv_filtration X n r).symm
  have h₂ := (Submodule.map_comp (SheafFormsAdapter.FormsAdapter.cohomologyEquiv X n).toLinearMap
    (nativeEquiv hBettiComparison X n).toLinearMap (FilteredComplexAdapter.FormsAdapter.filtration66 X n r)).symm
  have h₃ := congrArg (fun m => (FilteredComplexAdapter.FormsAdapter.filtration66 X n r).map m)
    (nativeEquiv_comp_forms hBettiComparison X n)
  exact h₁.trans (h₂.trans (h₃.trans (hBettiComparison.2.2 X P n r)))

theorem projectiveFiltration_one (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (r : ℤ) :
    AlgebraicGeometry.Comparison.Betti.Target.projectiveBettiHodgeFiltration P 1 r =
      if r ≤ 0 then ⊤ else if r = 1 then P.pureBettiSubspace 1 0 else ⊥ := by
  classical
  unfold AlgebraicGeometry.Comparison.Betti.Target.projectiveBettiHodgeFiltration
  by_cases hr : r ≤ 0
  · simp only [ite_eq_left hr]
  · rw [ite_eq_right hr, ite_eq_right hr]
    by_cases hr1 : r = 1
    · subst r
      rw [ite_eq_right (show ¬ ((1 : ℕ) : ℤ) < 1 by norm_num), ite_eq_left rfl]
      apply le_antisymm
      · refine iSup_le (fun p => iSup_le (fun hp => ?_))
        have hp1 : p = 1 := by apply Fin.ext; have := p.isLt; dsimp at *; omega
        subst p
        simp [AlgebraicGeometry.Comparison.Betti.Target.projectivePureBettiInDegree]
      · refine le_iSup_of_le (1 : Fin 2) (le_iSup_of_le (by norm_num) ?_)
        simp [AlgebraicGeometry.Comparison.Betti.Target.projectivePureBettiInDegree]
    · rw [ite_eq_right hr1, ite_eq_left (show ((1 : ℕ) : ℤ) < r by omega)]

end Betti.ComplexComparison

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

def Geometry.AbelianH1Model.nativeComplexComparison (hBettiComparison : Betti.ComparisonInput) (j : K →+* ℂ) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℂ (A.complexFiber j).scheme 1 ≃ₗ[ℂ] A.ComplexBetti j :=
  Betti.ComplexComparison.nativeEquiv hBettiComparison (A.complexFiber j).scheme 1

theorem Geometry.AbelianH1Model.nativeComplexComparison_filtration (hBettiComparison : Betti.ComparisonInput) (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)
    (r : ℤ) :
    (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℂ (A.complexFiber j).scheme 1 r).map
        (A.nativeComplexComparison hBettiComparison j).toLinearMap = A.bettiFiltration j P r :=
  (Betti.ComplexComparison.nativeEquiv_filtration hBettiComparison (A.complexFiber j).scheme P 1 r).trans
    (Betti.ComplexComparison.projectiveFiltration_one (A.smoothProjectiveFiber j P) r)

theorem Geometry.AbelianH1Model.complexDeRham_finite_of_BettiComparison (hBettiComparison : Betti.ComparisonInput) (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom) :
    FiniteDimensional ℂ (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℂ (A.complexFiber j).scheme 1) := by
  let := A.complexBetti_finiteDimensional j P
  exact (A.nativeComplexComparison hBettiComparison j).symm.finiteDimensional

end NumberTheory.PadicHodge.GeometricComparison

namespace NumberTheory.PadicHodge.GeometricComparison.Betti.ComplexComparison

/-! Naturality of BettiComparison's comparison after the proved native form and Betti universe transports. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem ulift_naturality {M N : ModuleCat.{0} ℂ} (f : M ⟶ N) :
    (ULift.moduleEquiv : ULift.{1} N ≃ₗ[ℂ] N).toLinearMap.comp
        ((ModuleCat.uliftFunctor.{1, 0} ℂ).map f).hom =
      f.hom.comp (ULift.moduleEquiv : ULift.{1} M ≃ₗ[ℂ] M).toLinearMap := rfl

theorem lower_square {M N U V U' V' : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup U] [AddCommGroup V]
    [AddCommGroup U'] [AddCommGroup V']
    [Module ℂ M] [Module ℂ N] [Module ℂ U] [Module ℂ V] [Module ℂ U'] [Module ℂ V']
    (a : M →ₗ[ℂ] N) (b : N →ₗ[ℂ] V) (c : M →ₗ[ℂ] U) (d : U →ₗ[ℂ] V)
    (u : U →ₗ[ℂ] U') (v : V →ₗ[ℂ] V') (d' : U' →ₗ[ℂ] V')
    (h : b.comp a = d.comp c) (hd : v.comp d = d'.comp u) :
    (v.comp b).comp a = d'.comp (u.comp c) := by
  rw [LinearMap.comp_assoc, h, ← LinearMap.comp_assoc, hd, LinearMap.comp_assoc]

theorem module_hom_square {M N U V : ModuleCat.{1} ℂ}
    (a : M ⟶ N) (b : N ⟶ V) (c : M ⟶ U) (d : U ⟶ V)
    (h : a ≫ b = c ≫ d) : b.hom.comp a.hom = d.hom.comp c.hom :=
  congrArg (fun f : M ⟶ V => f.hom) h

theorem lowerMap_naturality (hBettiComparison : ComparisonInput)
    {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth X.hom] [IsProper X.hom]
    [Smooth Y.hom] [IsProper Y.hom] (f : X ⟶ Y) (n : ℕ) :
    (AlgebraicGeometry.Comparison.Betti.Target.smoothDeRhamBettiLinearMap X n).comp (AlgebraicGeometry.Comparison.Betti.OpenForms.algebraicDeRhamPullback f n).hom =
      (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n f).hom.comp
        (AlgebraicGeometry.Comparison.Betti.Target.smoothDeRhamBettiLinearMap Y n) :=
  by
    unfold AlgebraicGeometry.Comparison.Betti.Target.smoothDeRhamBettiLinearMap
    exact lower_square (AlgebraicGeometry.Comparison.Betti.OpenForms.algebraicDeRhamPullback f n).hom
        (AlgebraicGeometry.Comparison.Betti.Smooth.ReferenceCongruence.smoothDeRhamBettiMap X n).hom (AlgebraicGeometry.Comparison.Betti.Smooth.ReferenceCongruence.smoothDeRhamBettiMap Y n).hom
        (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.bettiPullback f n).hom
        (AlgebraicGeometry.Comparison.Betti.Smooth.ReferenceCongruence.bettiDownEquiv Y n).toLinearMap (AlgebraicGeometry.Comparison.Betti.Smooth.ReferenceCongruence.bettiDownEquiv X n).toLinearMap
        (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n f).hom
        (module_hom_square _ _ _ _ (hBettiComparison.2.1 X Y f n)) (ulift_naturality _)

theorem cancel_comparison_square {M N M' N' U V : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
    [AddCommGroup U] [AddCommGroup V]
    [Module ℂ M] [Module ℂ N] [Module ℂ M'] [Module ℂ N'] [Module ℂ U] [Module ℂ V]
    (eM : M ≃ₗ[ℂ] M') (eN : N ≃ₗ[ℂ] N')
    (cM : M' →ₗ[ℂ] U) (cN : N' →ₗ[ℂ] V) (bM : M →ₗ[ℂ] U) (bN : N →ₗ[ℂ] V)
    (f : M →ₗ[ℂ] N) (f' : M' →ₗ[ℂ] N') (g : U →ₗ[ℂ] V)
    (hM : cM.comp eM.toLinearMap = bM) (hN : cN.comp eN.toLinearMap = bN)
    (he : f'.comp eM.toLinearMap = eN.toLinearMap.comp f)
    (hb : bN.comp f = g.comp bM) : cN.comp f' = g.comp cM := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := eM.surjective x
  change cN (f' (eM y)) = g (cM (eM y))
  rw [show f' (eM y) = eN (f y) from LinearMap.congr_fun he y]
  rw [show cN (eN (f y)) = bN (f y) from LinearMap.congr_fun hN (f y),
    show cM (eM y) = bM y from LinearMap.congr_fun hM y]
  exact LinearMap.congr_fun hb y

theorem nativeEquiv_naturality (hBettiComparison : ComparisonInput)
    {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth X.hom] [IsProper X.hom]
    [Smooth Y.hom] [IsProper Y.hom] (f : X ⟶ Y) (n : ℕ) :
    (nativeEquiv hBettiComparison X n).toLinearMap.comp (DeRham.Int.pullback f n) =
      (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n f).hom.comp (nativeEquiv hBettiComparison Y n).toLinearMap :=
  cancel_comparison_square (SheafFormsAdapter.FormsAdapter.cohomologyEquiv Y n) (SheafFormsAdapter.FormsAdapter.cohomologyEquiv X n)
    (nativeEquiv hBettiComparison Y n).toLinearMap (nativeEquiv hBettiComparison X n).toLinearMap
    (AlgebraicGeometry.Comparison.Betti.Target.smoothDeRhamBettiLinearMap Y n) (AlgebraicGeometry.Comparison.Betti.Target.smoothDeRhamBettiLinearMap X n)
    (AlgebraicGeometry.Comparison.Betti.OpenForms.algebraicDeRhamPullback f n).hom (DeRham.Int.pullback f n)
    (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n f).hom
    (nativeEquiv_comp_forms hBettiComparison Y n) (nativeEquiv_comp_forms hBettiComparison X n)
    (LinearMap.ext (fun x => (DeRham.AdapterNaturality.FormsAdapter.cohomologyEquiv_pullback f n x).symm))
    (lowerMap_naturality hBettiComparison f n)

end NumberTheory.PadicHodge.GeometricComparison.Betti.ComplexComparison

end

end OAI
