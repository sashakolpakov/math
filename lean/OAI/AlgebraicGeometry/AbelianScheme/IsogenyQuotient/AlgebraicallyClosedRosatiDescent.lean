import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RecoveredPicardInjection
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlgebraicallyClosedHomDescent
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RosatiBaseChange

/-! # Algebraically Closed Rosati Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlgebraicallyClosedRosatiDescent.Construction

noncomputable section

/-! Rosati compatibility descends across extensions of an
algebraically closed ground field, preserving the actual Poincare
class identity and the polarization adjoint equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RosatiBaseChange

set_option backward.isDefEq.respectTransparency false in
theorem field_poincare_pullback_injective
    {k K : Type} [Field k] [Field K] {g : ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (u : Spec (.of K) ⟶ Spec (.of k)) :
    Function.Injective (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (D.poincarePullbackOverMap u).left) := by
  have : Surjective u := ⟨Function.surjective_to_subsingleton _⟩
  let c := (Over.forget (Spec (.of K))).mapIso
    (Functor.Monoidal.μIso (Over.pullback u) D.abelian.scheme A.scheme)
  intro x y h
  apply IsogenyQuotient.Field.PicardInjection.Construction.field_abelian_picard_pullback_injective (PELModuli.CMPoints.AbelianProducts.abelianProduct D.abelian A) u
  apply (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackIso c).injective
  have hc : c.hom ≫ CategoryTheory.Limits.pullback.fst (D.abelian.scheme ⊗ A.scheme).hom u =
      (D.poincarePullbackOverMap u).left := AbelianModuli.HilbertConstruction.Pullback.Comparisons.poincareBaseChangeMap_eq_pullbackOverMap D u
  exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp c.hom _ x).symm.trans
    ((congrArg (fun q => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass q x) hc).trans
      (h.trans ((congrArg (fun q => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass q y) hc).symm.trans
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp c.hom _ y))))

set_option backward.isDefEq.respectTransparency false in
theorem rosati_of_algebraicallyClosed_field_pullback
    (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
    {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (ρ.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))))) : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ := by
  let u := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let F := Over.pullback u
  have : Surjective u := ⟨Function.surjective_to_subsingleton _⟩
  intro a
  obtain ⟨d', hd', hP, hpol⟩ := hρ a
  have : IsMonHom d' := hd'
  obtain ⟨d, hd, he⟩ := AlgebraicallyClosedHomDescent.Construction.algebraicallyClosed_field_hom_descends k K A.dual.abelian A.dual.abelian d'
  have : IsMonHom d := hd
  refine ⟨d, hd, ?_, ?_⟩
  · apply field_poincare_pullback_injective A.dual u
    have h₁ := AbelianModuli.ReferenceFamily.RosatiBaseChange.poincareEndomorphism_baseChange A.dual d (𝟙 A.abelian.scheme) u
    have h₂ := AbelianModuli.ReferenceFamily.RosatiBaseChange.poincareEndomorphism_baseChange A.dual (𝟙 A.dual.abelian.scheme) (ρ.map a) u
    rw [F.map_id, he] at h₁
    rw [F.map_id] at h₂
    exact h₁.symm.trans (hP.trans h₂)
  · apply F.map_injective
    rw [F.map_comp, F.map_comp, he]
    exact hpol

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlgebraicallyClosedRosatiDescent.Construction
