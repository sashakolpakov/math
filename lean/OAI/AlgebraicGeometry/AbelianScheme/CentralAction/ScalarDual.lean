import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.DualFactorization
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ScalarIsogeny
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Quotient
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.SideResidues

/-! # Scalar Dual -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ScalarDual.Construction

noncomputable section

/-! The Poincare dual of the principal scalar has a complementary dual
scalar. Its finite etale geometry follows from the same exact norm. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.NumberField
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [IsCMField E]
  [Field K] [CharZero K] {S : Scheme} {g N n : ℕ}
  (D : TateComparison.PEL.PELFamilyData (𝓞 E) g N S)

theorem scalarIsogeny_dual_rosati
    (hRosati : D.IsRosatiCompatible (IsCMField.ringOfIntegersComplexConj E).toRingHom)
    (β : 𝓞 E) (f : TateComparison.PELIsogenies.PELIsogeny D D n) (hf : f.isogeny.hom = Scalar.Construction.scalarMap D β) :
    D.polarizationMap.hom ≫ f.dualHom =
      Scalar.Construction.scalarMap D (IsCMField.ringOfIntegersComplexConj E β) ≫ D.polarizationMap.hom := by
  obtain ⟨bd, hp, hr⟩ := hRosati β
  have hd : f.dualHom = TateComparison.End.endSchemeMap D.dual.abelian.scheme bd := by
    apply Picard.Homomorphisms.PoincareDetection.Construction.poincareClass_injective D.dual D.dual.abelian.scheme
    have h := f.poincare
    rw [hf] at h
    exact congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard D.abelian.scheme).app (.op D.dual.abelian.scheme))
      (h.symm.trans hp)
  rw [hd]
  exact hr

theorem scalarIsogeny_dual_complements
    (hRosati : D.IsRosatiCompatible (IsCMField.ringOfIntegersComplexConj E).toRingHom)
    (β : 𝓞 E) (hnorm : β * IsCMField.ringOfIntegersComplexConj E β = n)
    (f : TateComparison.PELIsogenies.PELIsogeny D D n) (hf : f.isogeny.hom = Scalar.Construction.scalarMap D β) :
    ∃ c : TateComparison.End.IntegralEnd D.dual.abelian.scheme,
      f.dualHom ≫ TateComparison.End.endSchemeMap D.dual.abelian.scheme c = (𝟙 D.dual.abelian.scheme) ^ n ∧
      TateComparison.End.endSchemeMap D.dual.abelian.scheme c ≫ f.dualHom = (𝟙 D.dual.abelian.scheme) ^ n := by
  have hp := scalarIsogeny_dual_rosati D hRosati β f hf
  obtain ⟨c, _, hc⟩ := hRosati (IsCMField.ringOfIntegersComplexConj E β)
  change D.polarizationMap.hom ≫ TateComparison.End.endSchemeMap D.dual.abelian.scheme c =
    Scalar.Construction.scalarMap D (IsCMField.ringOfIntegersComplexConj E
      (IsCMField.ringOfIntegersComplexConj E β)) ≫ D.polarizationMap.hom at hc
  rw [SideResidues.Construction.integral_conjugation_involutive] at hc
  have hmult := Scalar.Construction.scalarMap_complements D β n hnorm
  have := Quotient.Construction.isogeny_effectiveEpi D.polarizationMap
  refine ⟨c, ?_, ?_⟩
  · apply (cancel_epi D.polarizationMap.hom).mp
    rw [← Category.assoc, hp, Category.assoc, hc, ← Category.assoc, hmult.2]
    simp only [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  · apply (cancel_epi D.polarizationMap.hom).mp
    rw [← Category.assoc, hc, Category.assoc, hp, ← Category.assoc, hmult.1]
    simp only [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]

/-- The actual Poincare dual of the marked scalar is a finite etale
surjection; this is proved without any assumed dual-isogeny theorem. -/
theorem scalarIsogeny_dual_finite_etale_surjective
    (base : S ⟶ Spec (.of K))
    (hRosati : D.IsRosatiCompatible (IsCMField.ringOfIntegersComplexConj E).toRingHom)
    (β : 𝓞 E) (hn : n ≠ 0)
    (hnorm : β * IsCMField.ringOfIntegersComplexConj E β = n)
    (f : TateComparison.PELIsogenies.PELIsogeny D D n) (hf : f.isogeny.hom = Scalar.Construction.scalarMap D β) :
    IsFinite f.dualHom.left ∧ Etale f.dualHom.left ∧ Surjective f.dualHom.left := by
  obtain ⟨c, hc, hc'⟩ := scalarIsogeny_dual_complements D hRosati β hnorm f hf
  have hpower := ScalarIsogeny.Construction.abelian_multiplier_finite_etale_surjective D.dual.abelian n
    (ScalarIsogeny.Construction.nat_unit_on_charZero_scheme base n hn)
  have := hpower.1
  have := hpower.2.1
  have := hpower.2.2
  have hsep (a : D.dual.abelian.scheme ⟶ D.dual.abelian.scheme) : IsSeparated a.left := by
    have : IsSeparated (a.left ≫ D.dual.abelian.scheme.hom) := by rw [a.w]; infer_instance
    exact IsSeparated.of_comp a.left D.dual.abelian.scheme.hom
  have := hsep f.dualHom
  have := hsep (TateComparison.End.endSchemeMap D.dual.abelian.scheme c)
  exact Descent.Construction.finite_etale_surjective_of_complements f.dualHom.left
    (TateComparison.End.endSchemeMap D.dual.abelian.scheme c).left ((𝟙 D.dual.abelian.scheme) ^ n).left
    (congrArg Over.Hom.left hc) (congrArg Over.Hom.left hc')

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ScalarDual.Construction
