import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyQuotientComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.QuotientFactor

/-! # Isogeny Diagram -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic

/-! Descend the original forward isogeny through the constructed arithmetic
quotient for its complementary isogeny. The multiplication identity supplies
the arithmetic composite; faithful flatness recovers the exact forward map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
  {A : Over (Spec (.of K))} [GrpObj A]
  {C : Over (Spec (.of ℂ))} [GrpObj C]
  {d : (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj A ⟶ C} [IsMonHom d]
  (D : IsogenyQuotient.ArithmeticIsogenyQuotient κ A d)

instance IsogenyQuotient.ArithmeticIsogenyQuotient.complexSourceIso_isMonHom : IsMonHom D.complexSourceIso.hom :=
  Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso_isMonHom D.baseExtension A

variable [IsCommMonObj A] [IsProper A.hom]

/-- Construct the original isogeny over the same arithmetic extension as
the complementary quotient, preserving its exact complex comparison. -/
theorem IsogenyQuotient.ArithmeticIsogenyQuotient.reverse_isogeny_descends
    (e : D.complexTarget ≅ C) [IsMonHom e.hom]
    (he : D.complexQuotient ≫ e.hom = d)
    (f : C ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj A) [IsMonHom f]
    [Etale f.left] [Surjective f.left]
    (n : ℕ) (hn : d ≫ f = (𝟙 _ : (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj A ⟶ _) ^ n) :
    ∃ r : D.target.toOver ⟶ (Over.pullback D.baseExtension.fieldExtension).obj A,
      IsMonHom r ∧ IsFinite r.left ∧ Etale r.left ∧ Surjective r.left ∧
        D.quotient ≫ r = (𝟙 _ : (Over.pullback D.baseExtension.fieldExtension).obj A ⟶ _) ^ n ∧
        (Over.pullback (Spec.map (CommRingCat.ofHom D.baseExtension.embedding))).map r ≫
          D.complexSourceIso.hom = e.hom ≫ f := by
  let ψ := Spec.map (CommRingCat.ofHom D.baseExtension.embedding)
  let F := Over.pullback ψ
  let A₀ := (Over.pullback D.baseExtension.fieldExtension).obj A
  let σ := D.complexSourceIso
  let h : F.obj D.target.toOver ⟶ F.obj A₀ := e.hom ≫ f ≫ σ.inv
  have : IsMonHom h := by
    change IsMonHom (e.hom ≫ f ≫ D.complexSourceIso.inv)
    infer_instance
  have hD : σ.inv ≫ F.map D.quotient ≫ e.hom = d :=
    (Category.assoc _ _ _).symm.trans he
  have hpower : F.map ((𝟙 A₀ : A₀ ⟶ A₀) ^ n) = (𝟙 (F.obj A₀) : F.obj A₀ ⟶ F.obj A₀) ^ n := by
    exact (map_pow F.homMonoidHom (𝟙 A₀) n).trans
      (congrArg (fun a => a ^ n) (F.map_id A₀))
  have hh : F.map D.quotient ≫ h = F.map ((𝟙 A₀ : A₀ ⟶ A₀) ^ n) :=
    (QuotientFactor.reverse_factor_of_power_composite σ (F.map D.quotient) e d f hD n hn).trans
      ((QuotientFactor.group_iso_conjugate_power σ n).trans hpower.symm)
  have : Flat ψ := inferInstance
  have : Surjective ψ := ⟨fun x => ⟨IsLocalRing.closedPoint ℂ, Subsingleton.elim _ x⟩⟩
  have : QuasiCompact ψ := inferInstance
  have : Flat D.quotient.left := D.flat
  have : Surjective D.quotient.left := D.surjective
  have : IsFinite D.quotient.left := D.finite
  obtain ⟨r, ⟨hr, hqr, hFr⟩, _⟩ := QuotientFactor.quotient_factor_descends ψ D.quotient
    ((𝟙 A₀ : A₀ ⟶ A₀) ^ n) h hh
  have hcompare : F.map r ≫ σ.hom = e.hom ≫ f := by
    rw [hFr]
    change (e.hom ≫ f ≫ σ.inv) ≫ σ.hom = e.hom ≫ f
    simp only [Category.assoc, σ.inv_hom_id, Category.comp_id]
  have : IsIso e.hom.left := ((Over.forget (Spec (.of ℂ))).mapIso e).isIso_hom
  have : IsIso σ.inv.left := ((Over.forget (Spec (.of ℂ))).mapIso σ).isIso_inv
  have hhEtale : Etale h.left := inferInstanceAs (Etale (e.hom.left ≫ f.left ≫ σ.inv.left))
  have hhSurj : Surjective h.left := inferInstanceAs (Surjective (e.hom.left ≫ f.left ≫ σ.inv.left))
  have hrEtale : Etale r.left := QuotientFactor.property_of_fpqc_baseChange ψ (@Etale) r (hFr.symm ▸ hhEtale)
  have hrSurj : Surjective r.left := QuotientFactor.property_of_fpqc_baseChange ψ (@Surjective) r (hFr.symm ▸ hhSurj)
  have : IsProper A₀.hom := inferInstanceAs (IsProper (pullback.snd A.hom D.baseExtension.fieldExtension))
  have : IsProper D.target.toOver.hom := D.target.proper
  have : IsProper (r.left ≫ A₀.hom) := r.w.symm ▸ D.target.proper
  have : IsProper r.left := IsProper.of_comp r.left A₀.hom
  have hrFinite : IsFinite r.left := AbelianScheme.TorsionQuotient.Quasi.TorsionGeometry.finite_of_proper_formallyUnramified r.left
  exact ⟨r, hr, hrFinite, hrEtale, hrSurj, hqr, hcompare⟩

end AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic

namespace AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.IsogenyDiagram

/-! Effective arithmetic descent of an entire isogeny into an arithmetic
abelian variety. Both the source scheme and the forward map are constructed,
with their actual group structures and exact complex-fiber comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ)
  (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (C : Over (Spec (.of ℂ))) [GrpObj C] [IsCommMonObj C]
  [Smooth C.hom] [IsProper C.hom] [GeometricallyConnected C.hom]

/-- Descend the complex source and its entire finite étale isogeny to
the chosen arithmetic target, preserving the original map exactly. -/
theorem finite_etale_isogeny_diagram_descends
    (f : C ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj A)
    [IsMonHom f] [IsFinite f.left] [Etale f.left] [Surjective f.left]
    (N : ℕ) (hN : N ≠ 0) :
    ∃ (B : Base.ArithmeticBaseExtension K κ)
      (Y : Quotients.FiniteDescent.AbelianQuotient.Construction.AbelianScheme (Spec (.of B.extension.carrier)))
      (r : Y.toOver ⟶ (Over.pullback B.fieldExtension).obj A)
      (e : (Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))).obj Y.toOver ≅ C),
      B.denominator = N ∧ IsMonHom e.hom ∧ IsMonHom r ∧
        IsFinite r.left ∧ Etale r.left ∧ Surjective r.left ∧
        (Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))).map r ≫
          (Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso B A).hom = e.hom ≫ f := by
  have : Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj A).hom :=
    inferInstanceAs (Smooth (pullback.snd A.hom (Spec.map (CommRingCat.ofHom κ))))
  have : IsProper ((Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj A).hom :=
    inferInstanceAs (IsProper (pullback.snd A.hom (Spec.map (CommRingCat.ofHom κ))))
  have : GeometricallyConnected ((Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj A).hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd A.hom (Spec.map (CommRingCat.ofHom κ))))
  obtain ⟨n, d, _, hd, hdFinite, hdEtale, hdSurj, _, hdf, _⟩ :=
    IsogenyComplementGeometry.exists_complementary_finite_etale_isogeny f
  let := hd
  let := hdFinite
  let := hdEtale
  let := hdSurj
  obtain ⟨D, hD, e, he, hDe⟩ := IsogenyQuotientComparison.finite_etale_isogeny_target_descends (f := d) N hN
  let := he
  obtain ⟨r, hr, hrFinite, hrEtale, hrSurj, _, hcompare⟩ :=
    D.reverse_isogeny_descends e hDe f n hdf
  exact ⟨D.baseExtension, D.target, r, e, hD, he, hr, hrFinite, hrEtale, hrSurj, hcompare⟩

end AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.IsogenyDiagram

end

end OAI
