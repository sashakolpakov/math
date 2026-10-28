import OAI.RepresentationTheory.Theta.Geometric.PELComplementDual

/-! # PEL Complement Compatibility -/

namespace OAI.RepresentationTheory.Theta.Geometric.PELComplementCompatibility

noncomputable section

/-! The actual complementary isogeny preserves the full integral action
and has precisely the original scalar polarization multiplier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {R k : Type} [CommRing R] [Field k] [CharZero k] [IsAlgClosed k]
    {g N q m : ℕ} [Fact q.Prime]
    {P Q : AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData R g N (Spec (.of k))}
    (e : AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny P Q (q ^ m))
    (δ : Fin g → ℕ) (hP : P.polarizationMap.HasPolarizationType δ)
    (hQ : Q.polarizationMap.HasPolarizationType δ) (hq : Nat.Coprime q (∏ i, δ i))

theorem isogeny_comp_complement :
    e.isogeny.hom ≫ (e.multiplierComplement δ hP hQ hq).hom = (𝟙 P.abelian.scheme) ^ (q ^ m) :=
  e.comp_multiplierComplementHom δ hP hQ hq

theorem complement_comp_isogeny :
    (e.multiplierComplement δ hP hQ hq).hom ≫ e.isogeny.hom = (𝟙 Q.abelian.scheme) ^ (q ^ m) :=
  e.multiplierComplementHom_comp δ hP hQ hq

theorem complementary_action (a : R) :
    AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap Q.abelian.scheme (Q.action a) ≫ (e.multiplierComplement δ hP hQ hq).hom =
      (e.multiplierComplement δ hP hQ hq).hom ≫ AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap P.abelian.scheme (P.action a) := by
  have := AlgebraicGeometry.AbelianScheme.CentralAction.Quotient.Construction.isogeny_effectiveEpi e.isogeny
  apply (cancel_epi e.isogeny.hom).mp
  calc
    _ = (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap P.abelian.scheme (P.action a) ≫ e.isogeny.hom) ≫
        (e.multiplierComplement δ hP hQ hq).hom := by
      rw [← Category.assoc, e.equivariant]
    _ = AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap P.abelian.scheme (P.action a) ≫ ((𝟙 P.abelian.scheme) ^ (q ^ m)) := by
      rw [Category.assoc, isogeny_comp_complement]
    _ = ((𝟙 P.abelian.scheme) ^ (q ^ m)) ≫ AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap P.abelian.scheme (P.action a) := by
      rw [MonObj.comp_pow, MonObj.pow_comp, Category.comp_id, Category.id_comp]
    _ = _ := by rw [← isogeny_comp_complement e δ hP hQ hq, Category.assoc]

theorem complementary_polarization :
    (e.multiplierComplement δ hP hQ hq).hom ≫ P.polarizationMap.hom ≫
        AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (e.multiplierComplement δ hP hQ hq).hom Q.dual P.dual =
      Q.polarizationMap.hom ^ (q ^ m) := by
  have := AlgebraicGeometry.AbelianScheme.CentralAction.Quotient.Construction.isogeny_effectiveEpi e.isogeny
  apply (cancel_epi e.isogeny.hom).mp
  calc
    _ = ((e.isogeny.hom ≫ (e.multiplierComplement δ hP hQ hq).hom) ≫ P.polarizationMap.hom) ≫
        AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (e.multiplierComplement δ hP hQ hq).hom Q.dual P.dual := by simp only [Category.assoc]
    _ = (((𝟙 P.abelian.scheme) ^ (q ^ m)) ≫ P.polarizationMap.hom) ≫
        AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (e.multiplierComplement δ hP hQ hq).hom Q.dual P.dual := by
      rw [isogeny_comp_complement]
    _ = (P.polarizationMap.hom ^ (q ^ m)) ≫
        AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (e.multiplierComplement δ hP hQ hq).hom Q.dual P.dual := by
      rw [MonObj.pow_comp, Category.id_comp]
    _ = (e.isogeny.hom ≫ Q.polarizationMap.hom ≫ e.dualHom) ≫
        AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (e.multiplierComplement δ hP hQ hq).hom Q.dual P.dual := by rw [e.polarization]
    _ = e.isogeny.hom ≫ Q.polarizationMap.hom ≫ ((𝟙 Q.dual.abelian.scheme) ^ (q ^ m)) := by
      simp only [Category.assoc]
      rw [PELComplementDual.complementary_dual_factor e δ hP hQ hq]
    _ = _ := by rw [MonObj.comp_pow, Category.comp_id]

end

end OAI.RepresentationTheory.Theta.Geometric.PELComplementCompatibility
