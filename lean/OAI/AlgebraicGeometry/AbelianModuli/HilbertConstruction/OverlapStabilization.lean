import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ImageAnnihilation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.ExtensionRestrictions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.ExtensionTransitions

/-! # Overlap Stabilization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Stabilize affine overlap equalities by increasing the tensor degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X Y Z : Scheme.{u}} {L : Y.Modules}

/-- Equality of section values persists after increasing the transition length. -/
theorem OverlapStabilization.powerTransition_value_eq_mono (s : Line.Bundles.structureModule Y ⟶ L) (n : ℕ)
    (U : Y.Opens) (v w : Γ(TensorPower.PowerSheaf.tensorPowerModule L n, U)) {m k : ℕ}
    (hm : (Power.SectionTransitions.powerSectionTransition s n m).app U v = (Power.SectionTransitions.powerSectionTransition s n m).app U w)
    (hmk : m ≤ k) :
    (Power.SectionTransitions.powerSectionTransition s n k).app U v = (Power.SectionTransitions.powerSectionTransition s n k).app U w := by
  induction k, hmk using Nat.le_induction with
  | base => exact hm
  | succ k _ ih =>
    exact congrArg (fun z : Γ(TensorPower.PowerSheaf.tensorPowerModule L (n + k), U) =>
      (Section.PowerMultiplication.multiplyPowerBySection s (n + k)).app U z) ih

/-- Finitely many eventual section-value equalities hold at one common degree. -/
theorem OverlapStabilization.powerTransition_value_eq_uniform {ι : Type v} [Fintype ι]
    (s : Line.Bundles.structureModule Y ⟶ L) (n : ℕ) (U : ι → Y.Opens)
    (v w : ∀ i, Γ(TensorPower.PowerSheaf.tensorPowerModule L n, U i))
    (h : ∀ i, ∃ m : ℕ, (Power.SectionTransitions.powerSectionTransition s n m).app (U i) (v i) =
      (Power.SectionTransitions.powerSectionTransition s n m).app (U i) (w i)) :
    ∃ m : ℕ, ∀ i, (Power.SectionTransitions.powerSectionTransition s n m).app (U i) (v i) =
      (Power.SectionTransitions.powerSectionTransition s n m).app (U i) (w i) := by
  classical
  choose m hm using h
  exact ⟨Finset.univ.sup m, fun i => OverlapStabilization.powerTransition_value_eq_mono s n (U i)
    (v i) (w i) (hm i) (Finset.le_sup (f := m) (Finset.mem_univ i))⟩

/-- A module map commutes with taking a local numerator's image-open value
and then restricting it to a smaller open. -/
theorem OverlapStabilization.image_section_postcomp_restrict (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} (t : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj M)
    (a : M ⟶ N) (W : Y.Opens) (hW : W ≤ f ''ᵁ ⊤) :
    N.presheaf.map (homOfLE hW).op
      (SectionsOnOpenImages.pullbackSectionImageEquiv f N (t ≫ (Scheme.Modules.pullback f).map a)) =
      a.app W (M.presheaf.map (homOfLE hW).op (SectionsOnOpenImages.pullbackSectionImageEquiv f M t)) := by
  exact (congrArg (fun z : Γ(N, f ''ᵁ ⊤) => N.presheaf.map (homOfLE hW).op z)
    (Open.ImageSectionMaps.pullbackSectionImageEquiv_postcomp f t a)).trans
      (ConcreteCategory.congr_hom (a.mapPresheaf.naturality (homOfLE hW).op)
        (SectionsOnOpenImages.pullbackSectionImageEquiv f M t)).symm

/-- On an affine framed common open, chart numerators agree after some degree transition. -/
theorem Common.DegreeChartExtensions.ChartPowerExtends.eventual_overlap_values
    (f : X ⟶ Y) (g : Z ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g]
    (s : Line.Bundles.structureModule Y ⟶ L) (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤)) (n : ℕ)
    (t : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj (TensorPower.PowerSheaf.tensorPowerModule L n))
    (t' : Line.Bundles.structureModule Z ⟶ (Scheme.Modules.pullback g).obj (TensorPower.PowerSheaf.tensorPowerModule L n))
    (ht : Common.DegreeChartExtensions.ChartPowerExtends f s r n t) (ht' : Common.DegreeChartExtensions.ChartPowerExtends g s r n t')
    (W : Y.Opens) [IsAffine W.toScheme]
    (e : Line.Bundles.structureModule W.toScheme ⟶ L.restrict W.ι) [IsIso e]
    (hWf : W ≤ f ''ᵁ ⊤) (hWg : W ≤ g ''ᵁ ⊤) :
    ∃ m : ℕ, (Power.SectionTransitions.powerSectionTransition s n m).app W
      ((TensorPower.PowerSheaf.tensorPowerModule L n).presheaf.map (homOfLE hWf).op
        (SectionsOnOpenImages.pullbackSectionImageEquiv f (TensorPower.PowerSheaf.tensorPowerModule L n) t)) =
      (Power.SectionTransitions.powerSectionTransition s n m).app W
        ((TensorPower.PowerSheaf.tensorPowerModule L n).presheaf.map (homOfLE hWg).op
          (SectionsOnOpenImages.pullbackSectionImageEquiv g (TensorPower.PowerSheaf.tensorPowerModule L n) t')) := by
  apply Affine.ImageAnnihilation.affine_open_power_equality W e s n
  have hleft := ConcreteCategory.congr_hom ((TensorPower.PowerSheaf.tensorPowerModule L n).presheaf.map_comp
    (homOfLE hWf).op (homOfLE (show W ⊓ Ample.LineBundles.sectionNonvanishing s ≤ W from inf_le_left)).op)
    (SectionsOnOpenImages.pullbackSectionImageEquiv f (TensorPower.PowerSheaf.tensorPowerModule L n) t)
  have hright := ConcreteCategory.congr_hom ((TensorPower.PowerSheaf.tensorPowerModule L n).presheaf.map_comp
    (homOfLE hWg).op (homOfLE (show W ⊓ Ample.LineBundles.sectionNonvanishing s ≤ W from inf_le_left)).op)
    (SectionsOnOpenImages.pullbackSectionImageEquiv g (TensorPower.PowerSheaf.tensorPowerModule L n) t')
  exact hleft.symm.trans ((Common.DegreeChartExtensions.ChartPowerExtends.agree_on f g s r n t t' ht ht'
    (W ⊓ Ample.LineBundles.sectionNonvanishing s) (inf_le_left.trans hWf) (inf_le_left.trans hWg)
    inf_le_right).trans hright)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
