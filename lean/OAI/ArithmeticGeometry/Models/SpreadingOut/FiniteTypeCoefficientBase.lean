import OAI.ArithmeticGeometry.Models.SpreadingOut.OpenModel
import OAI.ArithmeticGeometry.Models.SpreadingOut.Diagram

/-! # Finite Type Coefficient Base -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.FiniteTypeCoefficientBase.Construction

noncomputable section

/-! Replacing a finite type arithmetic base mapping to the number field
by a finite coefficient base preserves all base-change-stable properties. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u

theorem finiteType_coefficient_base
    {K : Type u} [Field K] [NumberField K]
    (S : Type u) [CommRing S] [Algebra (𝓞 K) S] [Algebra.FiniteType (𝓞 K) S]
    (φ : S →ₐ[𝓞 K] K) :
    ∃ (s : Finset K) (b : CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s ⟶ Spec (.of S)),
      CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s ≫ b = Spec.map (CommRingCat.ofHom φ.toRingHom) := by
  have hfg : φ.range.FG := by
    have : Algebra.FiniteType (𝓞 K) φ.range :=
      Algebra.FiniteType.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    exact φ.range.fg_iff_finiteType.mpr inferInstance
  obtain ⟨s, hs⟩ := hfg
  have hm (x : S) : φ x ∈ CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s := by
    change φ x ∈ Algebra.adjoin (𝓞 K) (s : Set K)
    rw [hs]
    exact φ.mem_range_self x
  let ψ : S →+* CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s := φ.toRingHom.codRestrict _ hm
  refine ⟨s, Spec.map (CommRingCat.ofHom ψ), ?_⟩
  change Spec.map (CommRingCat.ofHom (algebraMap (CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s) K)) ≫
    Spec.map (CommRingCat.ofHom ψ) = _
  rw [← Spec.map_comp]
  rfl

theorem finiteType_geometric_model_to_coefficient_model
    {K : Type u} [Field K] [NumberField K]
    (S : Type u) [CommRing S] [Algebra (𝓞 K) S] [Algebra.FiniteType (𝓞 K) S]
    (φ : S →ₐ[𝓞 K] K) (M : Over (Spec (.of S)))
    [Smooth M.hom] [IsProper M.hom] [GeometricallyIrreducible M.hom]
    (X : Over (Spec (.of K)))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom φ.toRingHom))).obj M ≅ X) :
    ∃ N : Foundations.Constructions.CoefficientModel K X,
      Smooth N.model.hom ∧ IsProper N.model.hom ∧ GeometricallyIrreducible N.model.hom := by
  obtain ⟨s, b, hb⟩ := finiteType_coefficient_base S φ
  let M₀ := (Over.pullback b).obj M
  let e₀ : (Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).obj M₀ ≅ X :=
    BaseChange.Constructions.Foundations.iteratedBaseChangeIso b _ M ≪≫ Scheme.Constructions.Foundations.baseChangeCongr hb M ≪≫ e
  let N : Foundations.Constructions.CoefficientModel K X := {
    coefficients := s
    model := M₀
    finitePresentation := ⟨inferInstanceAs (LocallyOfFinitePresentation (pullback.snd M.hom b)),
      inferInstanceAs (QuasiCompact (pullback.snd M.hom b)),
      inferInstanceAs (QuasiSeparated (pullback.snd M.hom b))⟩
    genericIso := e₀ }
  exact ⟨N, inferInstanceAs (Smooth (pullback.snd M.hom b)),
    inferInstanceAs (IsProper (pullback.snd M.hom b)),
    inferInstanceAs (GeometricallyIrreducible (pullback.snd M.hom b))⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.FiniteTypeCoefficientBase.Construction
