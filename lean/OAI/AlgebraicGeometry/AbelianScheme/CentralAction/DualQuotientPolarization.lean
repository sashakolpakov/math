import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.DualFactorization
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.EtaleCancellation
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Quotient

/-! # Dual Quotient Polarization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.DualQuotientPolarization.Construction

noncomputable section

/-! The constructed dual quotient map preserves the group law and
polarization. Finite etale cancellation uses connectedness and the origin. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {k R : Type} [Field k] [IsAlgClosed k] [CommRing R] {g N n : ℕ}
  {P Q : TateComparison.PEL.PELFamilyData R g N (Spec (.of k))}

/-- The two compatibility properties of the constructed quotient dual. -/
def QuotientDualCompatible
    (P Q : TateComparison.PEL.PELFamilyData R g N (Spec (.of k)))
    (e : Q.abelian.scheme ≅ P.abelian.scheme) [IsMonHom e.hom] : Prop :=
  IsMonHom (DualPicard.Construction.dualUnderlyingIso Q.dual P.dual e).inv ∧
    Q.polarizationMap.hom ≫ (DualPicard.Construction.dualUnderlyingIso Q.dual P.dual e).inv =
      e.hom ≫ P.polarizationMap.hom

omit [IsAlgClosed k] in
/-- The scalar dual's etaleness, already proved from its exact norm,
forces the quotient dual to preserve the group law and the polarization. -/
theorem dual_quotient_group_polarization
    (f : TateComparison.PELIsogenies.PELIsogeny P Q n) (g : TateComparison.PELIsogenies.PELIsogeny P P n)
    (e : Q.abelian.scheme ≅ P.abelian.scheme) [IsMonHom e.hom]
    (he : f.isogeny.hom ≫ e.hom = g.isogeny.hom)
    [IsFinite g.dualHom.left] [Etale g.dualHom.left] :
    QuotientDualCompatible P Q e := by
  change IsMonHom (DualPicard.Construction.dualUnderlyingIso Q.dual P.dual e).inv ∧
    Q.polarizationMap.hom ≫ (DualPicard.Construction.dualUnderlyingIso Q.dual P.dual e).inv =
      e.hom ≫ P.polarizationMap.hom
  let d := DualPicard.Construction.dualUnderlyingIso Q.dual P.dual e
  have hd : d.hom ≫ f.dualHom = g.dualHom := DualFactorization.Construction.dual_quotient_factorization f g e he
  have hd' : f.dualHom = d.inv ≫ g.dualHom := by
    rw [← hd, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have : IsIso d.inv.left := (Over.forget _).map_isIso d.inv
  have : IsFinite f.dualHom.left := by rw [hd', Over.comp_left]; infer_instance
  have : Etale f.dualHom.left := by rw [hd', Over.comp_left]; infer_instance
  have : IsMonHom (d.hom ≫ f.dualHom) := by rw [hd]; infer_instance
  have hzero : η[P.dual.abelian.scheme] ≫ d.hom = η[Q.dual.abelian.scheme] := by
    simpa only [MonObj.one_eq_one] using
      DualPicard.Construction.dualUnderlyingIso_preserves_origin Q.dual P.dual e (𝟙_ (Over (Spec (.of k))))
  have : IsMonHom d.hom := EtaleCancellation.Construction.abelian_map_isMonHom_of_finite_etale_comp
    P.dual.abelian Q.dual.abelian P.dual.abelian f.dualHom d.hom hzero
  have hp : Q.polarizationMap.hom ≫ f.dualHom =
      (e.hom ≫ P.polarizationMap.hom ≫ d.hom) ≫ f.dualHom := by
    have := Quotient.Construction.isogeny_effectiveEpi f.isogeny
    apply (cancel_epi f.isogeny.hom).mp
    calc
      _ = P.polarizationMap.hom ^ n := f.polarization
      _ = g.isogeny.hom ≫ P.polarizationMap.hom ≫ g.dualHom := g.polarization.symm
      _ = f.isogeny.hom ≫ ((e.hom ≫ P.polarizationMap.hom ≫ d.hom) ≫ f.dualHom) := by
        rw [← he, ← hd]
        simp only [Category.assoc]
  have hpol : Q.polarizationMap.hom = e.hom ≫ P.polarizationMap.hom ≫ d.hom :=
    EtaleCancellation.Construction.abelian_hom_ext_after_finite_etale Q.abelian Q.dual.abelian P.dual.abelian
      f.dualHom Q.polarizationMap.hom (e.hom ≫ P.polarizationMap.hom ≫ d.hom) hp
  refine ⟨inferInstanceAs (IsMonHom d.inv), ?_⟩
  change Q.polarizationMap.hom ≫ d.inv = e.hom ≫ P.polarizationMap.hom
  rw [hpol]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.DualQuotientPolarization.Construction
