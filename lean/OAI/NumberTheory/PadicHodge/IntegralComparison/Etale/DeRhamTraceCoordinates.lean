import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DeRhamTraceNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.FormScalarExtension

/-! # De Rham Trace Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DeRhamTraceCoordinates

noncomputable section

/-! The projection formula characterizes the native trace independently
of the polynomial étale coordinates used to construct it. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u v w

variable (R A B σ : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [Algebra (MvPolynomial σ R) A] [Algebra (MvPolynomial σ R) B]
  [IsScalarTower R (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) B]
  [IsScalarTower (MvPolynomial σ R) A B]
  [Algebra.FormallyEtale (MvPolynomial σ R) A]
  [Algebra.FormallyEtale (MvPolynomial σ R) B]
  [Fintype σ] [LinearOrder σ]
  {ι : Type v} [Fintype ι] (b : Module.Basis ι A B)

private theorem smul_symbol {S : Type u} [CommRing S] [Algebra R S]
    (n : ℕ) (x y : S) (v : Fin n → S) :
    x • AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R S y v =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R S (x * y) v := by
  rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one R S y v,
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one R S (x * y) v, smul_smul]

def formTrace (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n →ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n :=
  ((DeRhamTrace.trace R A B σ b).f n).hom

theorem trace_projection_formula (n : ℕ) (x : B) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    formTrace R A B σ b n (x • OrdinaryFormScalars.Ordinary.map R A B n ω) =
      Algebra.trace A B x • ω := by
  have he : (formTrace R A B σ b n).comp
      (x • (OrdinaryFormScalars.Ordinary.map R A B n).restrictScalars R) =
      Algebra.trace A B x • (LinearMap.id : Module.End R (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n)) := by
    apply DeRhamTraceNaturality.formMap_ext R A σ n
    intro a v
    change formTrace R A B σ b n
      (x • OrdinaryFormScalars.Ordinary.map R A B n
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R A σ ∘ v))) =
      Algebra.trace A B x •
        AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R A σ ∘ v)
    have hpb := DeRhamTraceNaturality.pullback_coordinate_symbol R A B σ n a v
    change OrdinaryFormScalars.Ordinary.map R A B n
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R A σ ∘ v)) = _ at hpb
    rw [hpb, smul_symbol]
    have ht := DeRhamTrace.trace_coordinate_symbol R A B σ b n (x * algebraMap A B a) v
    change formTrace R A B σ b n _ = _ at ht
    rw [ht, smul_symbol]
    congr 1
    calc
      Algebra.trace A B (x * algebraMap A B a) = Algebra.trace A B (a • x) := by
        rw [Algebra.smul_def, mul_comm]
      _ = a * Algebra.trace A B x := (Algebra.trace A B).map_smul a x
      _ = Algebra.trace A B x * a := mul_comm _ _
  exact LinearMap.congr_fun he ω

variable (τ : Type u) [Fintype τ] [LinearOrder τ]
  [Algebra (MvPolynomial τ R) A] [Algebra (MvPolynomial τ R) B]
  [IsScalarTower R (MvPolynomial τ R) A] [IsScalarTower R (MvPolynomial τ R) B]
  [IsScalarTower (MvPolynomial τ R) A B]
  [Algebra.FormallyEtale (MvPolynomial τ R) A]
  [Algebra.FormallyEtale (MvPolynomial τ R) B]
  {κ : Type w} [Fintype κ] (c : Module.Basis κ A B)

theorem trace_coordinate_independent : DeRhamTrace.trace R A B σ b = DeRhamTrace.trace R A B τ c := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  let e := (FormScalarExtension.isBaseChange R A B σ n).equiv
  obtain ⟨z, rfl⟩ := e.surjective ω
  change formTrace R A B σ b n (e z) = formTrace R A B τ c n (e z)
  induction z using TensorProduct.inductionOn with
  | tmul x η =>
    change formTrace R A B σ b n (x • OrdinaryFormScalars.Ordinary.map R A B n η) =
      formTrace R A B τ c n (x • OrdinaryFormScalars.Ordinary.map R A B n η)
    rw [trace_projection_formula, trace_projection_formula]
  | add x y hx hy => simp only [map_add, hx, hy]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DeRhamTraceCoordinates
