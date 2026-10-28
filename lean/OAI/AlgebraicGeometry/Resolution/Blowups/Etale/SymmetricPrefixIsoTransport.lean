import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.SymmetricControlPrefix
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonFactorization

/-! # Symmetric Prefix Iso Transport -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Symmetry of a complete actual prefix is preserved when its initial scheme is replaced by an isomorphic presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleSymmetric.of_isomorphic_comparison
    {b : ℕ} {X Y V W : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : V.IdealSheafData} {M : W.IdealSheafData}
    (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) (Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M)
    (H : P.EtaleSymmetric) (q : V ⟶ X) [IsIso q] (r : W ⟶ Y)
    (hc : P.EtaleComparison Q q r) (hf : q ≫ f = h) (hJ : J.comap q = L) : Q.EtaleSymmetric := by
  intro a _ ha hL
  let c := inv q ≫ a ≫ q
  let : Etale c := inferInstance
  have hqc : q ≫ c = a ≫ q := by simp [c, ← Category.assoc]
  have hcf : c ≫ f = f := by
    calc
      c ≫ f = inv q ≫ (a ≫ (q ≫ f)) := by simp only [c, Category.assoc]
      _ = inv q ≫ h := by rw [hf, ha]
      _ = f := by rw [← hf]; simp
  have hJc : J.comap c = J := by
    have he : (J.comap c).comap q = J.comap q := by
      rw [← Scheme.IdealSheafData.comap_comp, hqc, Scheme.IdealSheafData.comap_comp, hJ, hL]
    exact le_antisymm ((Affine.IdealChartDescent.Construction.idealSheaf_comap_le_iff_isIso _ _ q).mp he.le)
      ((Affine.IdealChartDescent.Construction.idealSheaf_comap_le_iff_isIso _ _ q).mp he.ge)
  obtain ⟨u, hu⟩ := H c hcf hJc
  have hcombined := hu.comp P P c u Q q r hc
  exact Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.exists_comparison_over_factor P Q Q q r (q ≫ c) (r ≫ u)
    hc hcombined a hqc.symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups
