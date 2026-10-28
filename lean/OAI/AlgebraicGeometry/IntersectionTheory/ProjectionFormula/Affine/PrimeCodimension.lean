import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FiltrationAvoidance

/-! # Prime Codimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrimeCodimension

noncomputable section

/-! On an actual affine open chart, a prime of the lowest allowed
ambient codimension is minimal in the module support. Its fixed
filtration multiplicity is therefore its genuine localized length. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FiltrationAvoidance

variable {R : Type} [CommRing R] {X : Scheme} (j : Spec (.of R) ⟶ X)

theorem antitone (p q : PrimeSpectrum R) (hpq : p.asIdeal ≤ q.asIdeal) :
    FiltrationAvoidance.support j q ≤ FiltrationAvoidance.support j p := by
  change closure ({j q} : Set X) ⊆ (FiltrationAvoidance.support j p : Set X)
  exact closure_minimal (Set.singleton_subset_iff.mpr (FiltrationAvoidance.mem j q p hpq)) (FiltrationAvoidance.support j p).isClosed

theorem injective [IsOpenImmersion j] : Function.Injective (FiltrationAvoidance.support j) := by
  intro p q he
  apply j.isOpenEmbedding.injective
  exact ((irreducibleSetEquivPoints (α := X)).apply_symm_apply (j p)).symm.trans
    ((congrArg (irreducibleSetEquivPoints (α := X)) he).trans
      ((irreducibleSetEquivPoints (α := X)).apply_symm_apply (j q)))

theorem minimal (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m V.structureMap] (j : Spec (.of R) ⟶ V.carrier) [IsOpenImmersion j]
    (M : ModuleCat R) (hM : ∀ v ∈ Module.support R M, q ≤ V.supportCodimension (FiltrationAvoidance.support j v))
    (p : PrimeSpectrum R) (hp : V.supportCodimension (FiltrationAvoidance.support j p) = q) :
    ∀ v ∈ Module.support R M, v.asIdeal ≤ p.asIdeal → v = p := by
  intro v hv hvp
  by_contra hn
  have hs : FiltrationAvoidance.support j p < FiltrationAvoidance.support j v :=
    lt_of_le_of_ne (antitone j v p hvp) (fun he => hn ((PrimeCodimension.injective j he).symm))
  have hc := Supports.codimension_strictAnti V m hs
  rw [hp] at hc
  exact (not_lt_of_ge (hM v hv)) hc

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrimeCodimension
