import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.FormsBaseQuotientSymbols

/-! # Base Quotient Differential -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PD.BaseQuotientDifferential

noncomputable section

/-!
# IntegralComparison: quotienting the coefficient base preserves the actual exterior differential
-/

universe u

theorem complex_d (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal A) (δ : DividedPowers I) (n : ℕ) :
    (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex R A I δ).d n (n + 1) = ModuleCat.ofHom (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δ n) :=
  CochainComplex.of_d (fun m => ModuleCat.of R (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ m))
    (fun m => ModuleCat.ofHom (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δ m)) n

theorem symbol_differential (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal A) (δ : DividedPowers I) (n : ℕ) (a : A) (v : Fin n → A) :
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δ n (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ a v) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ 1 (Fin.cons a v) :=
  AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.projectedDifferential_symbol R A I δ a v

variable (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
  (h : Function.Surjective (algebraMap R S)) (I : Ideal A) (δ : DividedPowers I)

theorem differential (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ n) :
    FormsBaseQuotientSymbols.formsEquiv R S A h I δ (n + 1) (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δ n ω) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential S A I δ n (FormsBaseQuotientSymbols.formsEquiv R S A h I δ n ω) := by
  obtain ⟨a, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.relations R A I δ n).mkQ_surjective ω
  obtain ⟨a, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n).mkQ_surjective a
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single v a =>
    change FormsBaseQuotientSymbols.formsEquiv R S A h I δ (n + 1)
      (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δ n (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ a v)) =
        AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential S A I δ n
          (FormsBaseQuotientSymbols.formsEquiv R S A h I δ n (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ a v))
    rw [symbol_differential, FormsBaseQuotientSymbols.formsEquiv_symbol,
      FormsBaseQuotientSymbols.formsEquiv_symbol, symbol_differential]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PD.BaseQuotientDifferential
