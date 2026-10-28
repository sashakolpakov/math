import OAI.AlgebraicGeometry.PELModuli.CMPoints.CountableEnhancedFiberImages
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Enhancement

/-! # Countable Group Fibers -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.CountableGroupFibers

noncomputable section

/-! Classifying maps into the original fine PEL model are countable
when the underlying complex fibers are group-isomorphic. All original
levels, polarizations, and integral actions enter the faithful code. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj Classical

theorem countable_PEL_classifying_maps_of_group_isos
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s N r : ℕ} [NeZero N]
    {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (b : Module.Basis (Fin r) ℤ (NumberField.RingOfIntegers E))
    {I : Type} (p : I → (Over.mk (Spec.map (CommRingCat.ofHom κ)) ⟶ M.space))
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N Foundations.Scheme.ProjectiveSpace.complexBase)
    (PA : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation A.abelian)
    (present : ∀ i, ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (M.universal.pullback (p i)).polarized.abelian)
    (e : ∀ i, A.abelian.scheme ≅ (M.universal.pullback (p i)).polarized.abelian.scheme)
    (he : ∀ i, IsMonHom (e i).hom) :
    (Set.range p).Countable := by
  apply CountableEnhancedFiberImages.countable_image_of_group_isomorphic_enhanced p
    (fun i => Enhancement.pelEnhancement b (M.universal.pullback (p i))) A PA present e he
  intro i j hij
  obtain ⟨hij⟩ := hij
  apply (Enhancement.pelClassifying_bijective M hM _).1
  exact Quotient.sound ⟨Enhancement.pelIsoOfEnhancement b hij⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.CountableGroupFibers
