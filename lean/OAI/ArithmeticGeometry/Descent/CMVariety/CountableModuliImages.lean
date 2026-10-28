import OAI.ArithmeticGeometry.Descent.CMVariety.UnpolarizedComparisons
import OAI.ArithmeticGeometry.Descent.CMVariety.CountablePolarizationMaps
import OAI.ArithmeticGeometry.Descent.CMVariety.CountableEncodings
import OAI.ArithmeticGeometry.Descent.CMVariety.ModuliFiberFaithfulness

/-! # Countable Moduli Images -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-! With the arithmetic embedding fixed, full-level enhanced fibers
isomorphic apart from polarization have only countably many classifying
maps. Actual transported polarization maps provide the countable code. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem StandardModuli.Abelian.ArithmeticAbelianModuli.countable_image_of_unpolarized_comparisons
    (M : StandardModuli.Abelian.ArithmeticAbelianModuli) {I : Type*} (p : I → (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ M.space))
    (A : ModuliObjects.Abelian.EnhancedAbelianData M.dimension M.polarizationType M.level M.endomorphismCount AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : StandardModuli.Abelian.ComplexAbelianPresentation A.polarized.abelian)
    (e : ∀ i, UnpolarizedComparisons.Abelian.UnpolarizedEnhancedIso A (M.universal.pullback (p i)))
    (hbase : ∀ i j, p i ≫ M.parameter.hom = p j ≫ M.parameter.hom) :
    (Set.range p).Countable := by
  let Code := {f : A.polarized.abelian.scheme ⟶ A.polarized.dual.abelian.scheme // IsMonHom f}
  let : Countable Code := CountablePolarizationMaps.Abelian.dual_group_maps_countable A.polarized P
  let code (i : I) : Code := ⟨(e i).transportedPolarization, inferInstance⟩
  apply CountableEncodings.Abelian.countable_range_of_countable_encoding code p
  intro i j hij
  exact M.morphism_eq_of_enhanced_fiber_iso (p i) (p j) (hbase i j)
    ⟨(e i).enhancedIsoOfTransportedEq (e j) (congrArg Subtype.val hij)⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety
