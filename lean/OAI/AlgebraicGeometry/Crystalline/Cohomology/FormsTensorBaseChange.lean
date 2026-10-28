import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateFormBasis
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.ExteriorPowerBaseChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExteriorPowerCongr
import OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.TwoFormsBaseChange

/-! # Forms Tensor Base Change -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FormsTensorBaseChange.EtaleFormsTensorBaseChange

noncomputable section

/-! All degrees of ordinary forms on etale coordinate charts commute with flat integral scalar extension. -/

open scoped TensorProduct

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u
variable (R S A B σ τ : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B] [Module.Flat R S]
  [LinearOrder σ] [LinearOrder τ]
  [Algebra (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) A]
  [Algebra.FormallyEtale (MvPolynomial σ R) A]
  [Algebra (MvPolynomial τ S) B] [IsScalarTower S (MvPolynomial τ S) B]
  [Algebra.FormallyEtale (MvPolynomial τ S) B]

def tensorEquiv (n : ℕ) : B ⊗[A] DeRhamPresentationTo.DeRhamPresentation.Form R A n ≃ₗ[B] DeRhamPresentationTo.DeRhamPresentation.Form S B n := by
  let : Module.Flat A B := NumberTheory.PadicHodge.GeometricComparison.Integral.TwoFormsBaseChange.IntegralTwoFormsBaseChange.affineFlat R S A B
  exact ((NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateFormBasis.exteriorEquiv R A σ n).baseChange A B _ _).trans
    ((NumberTheory.PadicHodge.GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerEquiv A B (KaehlerDifferential R A) n).trans
      ((NumberTheory.PadicHodge.GeometricComparison.ExteriorPowerCongr.ExteriorBaseChange.powerCongr n (KaehlerDifferential.tensorKaehlerEquiv R S A B)).trans
        (NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateFormBasis.exteriorEquiv S B τ n).symm))

theorem tensorEquiv_symbol (n : ℕ) (b : B) (a : A) (v : Fin n → A) :
    tensorEquiv R S A B σ τ n (b ⊗ₜ[A] DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      DeRhamPresentationTo.DeRhamPresentation.symbol S B (b * algebraMap A B a) (fun i => algebraMap A B (v i)) := by
  let : Module.Flat A B := NumberTheory.PadicHodge.GeometricComparison.Integral.TwoFormsBaseChange.IntegralTwoFormsBaseChange.affineFlat R S A B
  have he (c : A) (w : Fin n → A) : NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateFormBasis.exteriorEquiv R A σ n (DeRhamPresentationTo.DeRhamPresentation.symbol R A c w) =
      c • DeRhamPresentationTo.DeRhamPresentation.exteriorSymbol R A n w :=
    (LinearMap.congr_fun (NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateFormBasis.exteriorEquiv_eq R A σ n) _).trans (DeRhamPresentationTo.DeRhamPresentation.toExterior_symbol R A c w)
  have hf (c : B) (w : Fin n → B) : NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateFormBasis.exteriorEquiv S B τ n (DeRhamPresentationTo.DeRhamPresentation.symbol S B c w) =
      c • DeRhamPresentationTo.DeRhamPresentation.exteriorSymbol S B n w :=
    (LinearMap.congr_fun (NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateFormBasis.exteriorEquiv_eq S B τ n) _).trans (DeRhamPresentationTo.DeRhamPresentation.toExterior_symbol S B c w)
  apply (NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateFormBasis.exteriorEquiv S B τ n).injective
  simp only [tensorEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.baseChange_tmul, he, hf, DeRhamPresentationTo.DeRhamPresentation.exteriorSymbol, TensorProduct.tmul_smul]
  refine (congrArg (NumberTheory.PadicHodge.GeometricComparison.ExteriorPowerCongr.ExteriorBaseChange.powerCongr n (KaehlerDifferential.tensorKaehlerEquiv R S A B))
    (NumberTheory.PadicHodge.GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerEquiv_tmul_ιMulti A B (KaehlerDifferential R A) n
      (a • b) (fun i => KaehlerDifferential.D R A (v i)))).trans ?_
  rw [map_smul, NumberTheory.PadicHodge.GeometricComparison.ExteriorPowerCongr.ExteriorBaseChange.powerCongr_ιMulti]
  have h : (fun i => KaehlerDifferential.tensorKaehlerEquiv R S A B
      (1 ⊗ₜ[A] KaehlerDifferential.D R A (v i))) =
      fun i => KaehlerDifferential.D S B (algebraMap A B (v i)) := by
    funext i
    exact (KaehlerDifferential.tensorKaehlerEquiv_tmul_D R S A B 1 (v i)).trans (one_smul B _)
  rw [h, Algebra.smul_def, mul_comm]

def scalarEquiv (n : ℕ) : S ⊗[R] DeRhamPresentationTo.DeRhamPresentation.Form R A n ≃ₗ[S] DeRhamPresentationTo.DeRhamPresentation.Form S B n :=
  (Algebra.IsPushout.cancelBaseChange R S A B (DeRhamPresentationTo.DeRhamPresentation.Form R A n)).symm.trans
    ((tensorEquiv R S A B σ τ n).restrictScalars S)

theorem scalarEquiv_symbol (n : ℕ) (s : S) (a : A) (v : Fin n → A) :
    scalarEquiv R S A B σ τ n (s ⊗ₜ[R] DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      DeRhamPresentationTo.DeRhamPresentation.symbol S B (algebraMap S B s * algebraMap A B a) (fun i => algebraMap A B (v i)) := by
  change tensorEquiv R S A B σ τ n
    ((Algebra.IsPushout.cancelBaseChange R S A B (DeRhamPresentationTo.DeRhamPresentation.Form R A n)).symm
      (s ⊗ₜ[R] DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) = _
  rw [Algebra.IsPushout.cancelBaseChange_symm_tmul, tensorEquiv_symbol]

theorem scalarEquiv_eq_map (n : ℕ) :
    (scalarEquiv R S A B σ τ n).toLinearMap = NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarMap.FormsBaseChange.formScalarMap R S A B n := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s ω
  obtain ⟨x, rfl⟩ := (DeRhamPresentationTo.DeRhamPresentation.relations R A n).mkQ_surjective ω
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
  | single v a =>
    exact (scalarEquiv_symbol R S A B σ τ n s a v).trans
      (NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarMap.FormsBaseChange.formScalarMap_symbol R S A B s a v).symm

theorem differential (n : ℕ) (x : S ⊗[R] DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    scalarEquiv R S A B σ τ (n + 1) ((DeRhamPresentationTo.DeRhamPresentation.differential R A n).baseChange S x) =
      DeRhamPresentationTo.DeRhamPresentation.differential S B n (scalarEquiv R S A B σ τ n x) := by
  change (scalarEquiv R S A B σ τ (n + 1)).toLinearMap ((DeRhamPresentationTo.DeRhamPresentation.differential R A n).baseChange S x) =
    DeRhamPresentationTo.DeRhamPresentation.differential S B n ((scalarEquiv R S A B σ τ n).toLinearMap x)
  rw [scalarEquiv_eq_map, scalarEquiv_eq_map]
  exact NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarMap.FormsBaseChange.formScalarMap_differential R S A B n x

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FormsTensorBaseChange.EtaleFormsTensorBaseChange
