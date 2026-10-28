import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.DividedPowerDescent
import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.ChartDividedPowers
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.StandardEtaleCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.IdealTransport

/-! # Smooth Divided Powers -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothDividedPowers

noncomputable section

/-! The canonical divided powers on the special-fiber ideal of any
smooth algebra over a finite Witt level, obtained from actual standard
étale charts and equality detection on a principal affine cover. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (A : Type) [CommRing A] [Algebra (Witt.Ring p k n) A]
  [Algebra.Smooth (Witt.Ring p k n) A]

local notation "W" => WittVector p k
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n

def localizers : Finset A :=
  (IntegralComparison.Smooth.StandardEtaleCoordinates.exists_finite_cover S A).choose

omit [Fintype k] [CharP k p] in
theorem localizers_span : Ideal.span (localizers p k n A : Set A) = ⊤ :=
  (IntegralComparison.Smooth.StandardEtaleCoordinates.exists_finite_cover S A).choose_spec.2

abbrev Index := {a : A // a ∈ localizers p k n A}

omit [Fintype k] [CharP k p] in
private theorem coordinates (i : Index p k n A) :
    IntegralComparison.Smooth.StandardEtaleCoordinates.HasCoordinates S A i.val :=
  (IntegralComparison.Smooth.StandardEtaleCoordinates.exists_finite_cover S A).choose_spec.1 i.val i.property

def coordinateCount (i : Index p k n A) : ℕ := (coordinates p k n A i).choose

instance coordinateAlgebra (i : Index p k n A) :
    Algebra (MvPolynomial (Fin (coordinateCount p k n A i)) S) (Localization.Away i.val) :=
  (coordinates p k n A i).choose_spec.choose

instance coordinateTower (i : Index p k n A) :
    IsScalarTower S (MvPolynomial (Fin (coordinateCount p k n A i)) S)
      (Localization.Away i.val) :=
  (coordinates p k n A i).choose_spec.choose_spec.1

instance coordinateStandardEtale (i : Index p k n A) :
    Algebra.IsStandardEtale (MvPolynomial (Fin (coordinateCount p k n A i)) S)
      (Localization.Away i.val) :=
  (coordinates p k n A i).choose_spec.choose_spec.2

def presentation (i : Index p k n A) :
    StandardEtalePresentation (MvPolynomial (Fin (coordinateCount p k n A i)) S)
      (Localization.Away i.val) := Classical.choice inferInstance

def chartDividedPowers (i : Index p k n A) : DividedPowers (Ideal.span {(p : Localization.Away i.val)}) :=
  ChartDividedPowers.dividedPowers p k n (Fin (coordinateCount p k n A i))
    (Localization.Away i.val) (presentation p k n A i)

omit [Fintype k] in
theorem chart_base (i : Index p k n A) :
    DividedPowers.IsDPMorphism (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
      (chartDividedPowers p k n A i)
      ((algebraMap S (Localization.Away i.val)).comp (Witt.quotient p k n)) :=
  ChartDividedPowers.wittBase_isDPMorphism p k n (Fin (coordinateCount p k n A i))
    (Localization.Away i.val) (presentation p k n A i)

omit [Fintype k] in
private theorem exists_dividedPowers :
    ∃ δ : DividedPowers (Ideal.span {(p : A)}),
      DividedPowers.IsDPMorphism (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) δ
        ((algebraMap S A).comp (Witt.quotient p k n)) := by
  let := ChartDeRham.sourceWittAlgebra p k n A
  let : IsScalarTower W S A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let B : Index p k n A → Type := fun i => Localization.Away i.val
  have heB (i : Index p k n A) : Ideal.span {algebraMap W (B i) (p : W)} =
      Ideal.span {(p : B i)} := congrArg (fun a : B i => Ideal.span {a})
        (map_natCast (algebraMap W (B i)) p)
  let δ : ∀ i, DividedPowers (Ideal.span {algebraMap W (B i) (p : W)}) :=
    fun i => (heB i).symm ▸ chartDividedPowers p k n A i
  let f : ∀ i, A →ₐ[W] B i := fun i => IsScalarTower.toAlgHom W A (B i)
  have hb (i : Index p k n A) :
      DividedPowers.IsDPMorphism (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
        (δ i) (algebraMap W (B i)) := by
    have he : algebraMap W (B i) =
        (algebraMap S (Localization.Away i.val)).comp (Witt.quotient p k n) := by
      ext w
      rfl
    exact DividedPower.IdealTransport.isDPMorphism (heB i).symm _ _ _
      (he ▸ chart_base p k n A i)
  have hi : ∀ x y : A, (∀ i, f i x = f i y) → x = y := by
    intro x y h
    apply Localization.algebraMap_injective_of_span_eq_top (localizers p k n A : Set A)
      (localizers_span p k n A)
    funext i
    exact h i
  have hd : ∃ δA : DividedPowers (Ideal.span {algebraMap W A (p : W)}),
      DividedPowers.IsDPMorphism (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
        δA (algebraMap W A) :=
    ⟨Principal.DividedPowerDescent.dividedPowers W (p : W)
      (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) A B δ f hb hi,
      Principal.DividedPowerDescent.base_isDPMorphism W (p : W)
        (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) A B δ f hb hi⟩
  obtain ⟨δA, hδA⟩ := hd
  have heA : Ideal.span {algebraMap W A (p : W)} = Ideal.span {(p : A)} :=
    congrArg (fun a : A => Ideal.span {a}) (map_natCast (algebraMap W A) p)
  exact ⟨heA ▸ δA, DividedPower.IdealTransport.isDPMorphism heA _ _ _ hδA⟩

def dividedPowers : DividedPowers (Ideal.span {(p : A)}) :=
  (exists_dividedPowers p k n A).choose

omit [Fintype k] in
theorem wittBase_isDPMorphism :
    DividedPowers.IsDPMorphism (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
      (dividedPowers p k n A) ((algebraMap S A).comp (Witt.quotient p k n)) :=
  (exists_dividedPowers p k n A).choose_spec

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothDividedPowers
