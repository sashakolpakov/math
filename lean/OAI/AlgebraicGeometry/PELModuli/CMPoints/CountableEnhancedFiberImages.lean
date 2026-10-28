import OAI.AlgebraicGeometry.PELModuli.CMPoints.EnhancementTransportCodes
import OAI.AlgebraicGeometry.PELModuli.CMPoints.CountableFiberImages
import OAI.ArithmeticGeometry.Descent.CMVariety.CountableEncodings

/-! # Countable Enhanced Fiber Images -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.CountableEnhancedFiberImages

noncomputable section

/-! The countability argument applies directly to any classifying
family that is faithful on the original enhanced fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj Classical

open OAI.ArithmeticGeometry.Descent.CMVariety.CountableEncodings.Abelian

theorem countable_image_of_unpolarized_enhanced_isos
    {g N r : ℕ} {δ : Fin g → ℕ} {I X : Type}
    (p : I → X) (B : I → ArithmeticGeometry.Descent.CMVariety.ModuliObjects.Abelian.EnhancedAbelianData g δ N r Foundations.Scheme.ProjectiveSpace.complexBase)
    (A : ArithmeticGeometry.Descent.CMVariety.ModuliObjects.Abelian.EnhancedAbelianData g δ N r Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation A.polarized.abelian)
    (e : ∀ i, ArithmeticGeometry.Descent.CMVariety.UnpolarizedComparisons.Abelian.UnpolarizedEnhancedIso A (B i))
    (hfaithful : ∀ i j, Nonempty (ArithmeticGeometry.Descent.CMVariety.ModuliObjects.Abelian.EnhancedAbelianIso (B i) (B j)) → p i = p j) :
    (Set.range p).Countable := by
  let Code := {f : A.polarized.abelian.scheme ⟶ A.polarized.dual.abelian.scheme // IsMonHom f}
  let : Countable Code := ArithmeticGeometry.Descent.CMVariety.CountablePolarizationMaps.Abelian.dual_group_maps_countable A.polarized P
  let code := fun i => (⟨(e i).transportedPolarization, inferInstance⟩ : Code)
  apply ArithmeticGeometry.Descent.CMVariety.CountableEncodings.Abelian.countable_range_of_countable_encoding code p
  intro i j hij
  exact hfaithful i j ⟨(e i).enhancedIsoOfTransportedEq (e j) (congrArg Subtype.val hij)⟩

theorem countable_image_of_group_isomorphic_enhanced
    {g N r : ℕ} {δ : Fin g → ℕ} [NeZero N] {I X : Type}
    (p : I → X) (B : I → ArithmeticGeometry.Descent.CMVariety.ModuliObjects.Abelian.EnhancedAbelianData g δ N r Foundations.Scheme.ProjectiveSpace.complexBase)
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation A.abelian)
    (present : ∀ i, ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (B i).polarized.abelian)
    (e : ∀ i, A.abelian.scheme ≅ (B i).polarized.abelian.scheme)
    (he : ∀ i, IsMonHom (e i).hom)
    (hfaithful : ∀ i j, Nonempty (ArithmeticGeometry.Descent.CMVariety.ModuliObjects.Abelian.EnhancedAbelianIso (B i) (B j)) → p i = p j) :
    (Set.range p).Countable := by
  let (i : I) : IsMonHom (e i).hom := he i
  let Code := EnhancementTransportCodes.EnhancementTransportCode A.abelian N r
  let : Countable Code := EnhancementTransportCodes.enhancementTransportCode_countable A.abelian A.level P
  let code := fun i => EnhancementTransportCodes.enhancementTransportCode A.abelian (B i) (e i)
  apply CountableFiberImages.countable_range_of_countable_code_fiber_images code p
  intro c
  let J := {i : I // code i = c}
  by_cases hn : Nonempty J
  · let j₀ : J := Classical.choice hn
    apply countable_image_of_unpolarized_enhanced_isos (fun j : J => p j) (fun j : J => B j)
      (B j₀) (present j₀)
    · intro j
      exact EnhancementTransportCodes.unpolarizedComparisonOfTransportCodeEq A.abelian (B j₀) (B j) (e j₀) (e j)
        (j₀.property.trans j.property.symm)
    · intro i j hij
      exact hfaithful i j hij
  · let : IsEmpty J := not_nonempty_iff.mp hn
    exact Set.countable_range (fun j : J => p j)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.CountableEnhancedFiberImages
