import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.MultiplicationRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.AffineAnnihilation

/-! # Restricted Power Annihilation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictedPowerAnnihilation

noncomputable section

/-!
Affine annihilation for numerators valued in restrictions and pullbacks of the
original tensor powers, using compatibility of the global transition maps.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {L : Y.Modules}

theorem pullbackSection_sub (f : X ⟶ Y) (s t : Line.Bundles.structureModule Y ⟶ L) :
    Ample.LineBundles.pullbackSection f (s - t) = Ample.LineBundles.pullbackSection f s - Ample.LineBundles.pullbackSection f t :=
  (congrArg (fun a : (Scheme.Modules.pullback f).obj (Line.Bundles.structureModule Y) ⟶
      (Scheme.Modules.pullback f).obj L => (Line.Bundles.structureModulePullbackIso f).inv ≫ a)
    ((Scheme.Modules.pullback f).map_sub (f := s) (g := t))).trans (Preadditive.comp_sub _ _ _)

variable (f : X ⟶ Y) [IsOpenImmersion f] [IsAffine X]

/-- An affine frame kills numerator differences in restrictions of the original
power sheaves by applying a sufficiently long global transition map. -/
theorem restricted_power_annihilation (e : Line.Bundles.structureModule X ⟶ L.restrict f) [IsIso e]
    (s : Line.Bundles.structureModule Y ⟶ L) (n : ℕ)
    (t : Line.Bundles.structureModule X ⟶ (TensorPower.PowerSheaf.tensorPowerModule L n).restrict f)
    (ht : Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing (Section.SectionRestriction.restrictSection f s)).ι t = 0) :
    ∃ m : ℕ, t ≫ (Scheme.Modules.restrictFunctor f).map (Power.SectionTransitions.powerSectionTransition s n m) = 0 := by
  let D := Ample.LineBundles.sectionNonvanishing (Section.SectionRestriction.restrictSection f s)
  let E := TensorPower.RestrictionMaps.tensorPowerRestrictIso f L n
  let t₀ := t ≫ E.inv
  have ht₀ : Ample.LineBundles.pullbackSection D.ι t₀ = 0 :=
    (Power.SectionTransitions.pullbackSection_postcomp D.ι t E.inv).trans (by rw [ht, zero_comp])
  obtain ⟨m, hm⟩ := Framed.AffineAnnihilation.framed_affine_power_annihilation e (Section.SectionRestriction.restrictSection f s) n t₀ ht₀
  refine ⟨m, ?_⟩
  calc
    t ≫ (Scheme.Modules.restrictFunctor f).map (Power.SectionTransitions.powerSectionTransition s n m) =
        t₀ ≫ (E.hom ≫ (Scheme.Modules.restrictFunctor f).map (Power.SectionTransitions.powerSectionTransition s n m)) := by
      simp only [t₀, Category.assoc, Iso.inv_hom_id_assoc]
    _ = t₀ ≫ (Power.SectionTransitions.powerSectionTransition (Section.SectionRestriction.restrictSection f s) n m ≫
        (TensorPower.RestrictionMaps.tensorPowerRestrictIso f L (n + m)).hom) :=
      congrArg (fun a => t₀ ≫ a) (Power.MultiplicationRestriction.tensorPowerRestrictIso_transition f s n m)
    _ = (t₀ ≫ Power.SectionTransitions.powerSectionTransition (Section.SectionRestriction.restrictSection f s) n m) ≫
        (TensorPower.RestrictionMaps.tensorPowerRestrictIso f L (n + m)).hom := (Category.assoc _ _ _).symm
    _ = 0 := by rw [hm, zero_comp]

/-- The annihilation result also holds in the canonical pullback sheaves used
by the affine-chart extension construction. -/
theorem affine_chart_power_annihilation
    (e : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj L) [IsIso e]
    (s : Line.Bundles.structureModule Y ⟶ L) (n : ℕ)
    (t : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj (TensorPower.PowerSheaf.tensorPowerModule L n))
    (ht : Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)).ι t = 0) :
    ∃ m : ℕ, t ≫ (Scheme.Modules.pullback f).map (Power.SectionTransitions.powerSectionTransition s n m) = 0 := by
  let E := Scheme.Modules.restrictFunctorIsoPullback f
  let e₀ : Line.Bundles.structureModule X ⟶ L.restrict f := e ≫ (E.app L).inv
  have : IsIso e₀ := inferInstanceAs (IsIso (e ≫ (E.app L).inv))
  let t₀ := t ≫ (E.app (TensorPower.PowerSheaf.tensorPowerModule L n)).inv
  have hD : Ample.LineBundles.sectionNonvanishing (Section.SectionRestriction.restrictSection f s) = Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s) :=
    (Section.SectionRestriction.sectionNonvanishing_restrictSection f s).trans (Section.Nonvanishing.sectionNonvanishing_pullback f s).symm
  have ht' : Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing (Section.SectionRestriction.restrictSection f s)).ι t = 0 := by
    rw [hD]
    exact ht
  have ht₀ : Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing (Section.SectionRestriction.restrictSection f s)).ι t₀ = 0 :=
    (Power.SectionTransitions.pullbackSection_postcomp _ t (E.app (TensorPower.PowerSheaf.tensorPowerModule L n)).inv).trans (by rw [ht', zero_comp])
  obtain ⟨m, hm⟩ := restricted_power_annihilation f e₀ s n t₀ ht₀
  refine ⟨m, ?_⟩
  calc
    t ≫ (Scheme.Modules.pullback f).map (Power.SectionTransitions.powerSectionTransition s n m) =
        t₀ ≫ ((E.app (TensorPower.PowerSheaf.tensorPowerModule L n)).hom ≫
          (Scheme.Modules.pullback f).map (Power.SectionTransitions.powerSectionTransition s n m)) := by
      simp only [t₀, Category.assoc, Iso.inv_hom_id_assoc]
    _ = t₀ ≫ ((Scheme.Modules.restrictFunctor f).map (Power.SectionTransitions.powerSectionTransition s n m) ≫
        (E.app (TensorPower.PowerSheaf.tensorPowerModule L (n + m))).hom) :=
      congrArg (fun a => t₀ ≫ a) (E.hom.naturality (Power.SectionTransitions.powerSectionTransition s n m)).symm
    _ = (t₀ ≫ (Scheme.Modules.restrictFunctor f).map (Power.SectionTransitions.powerSectionTransition s n m)) ≫
        (E.app (TensorPower.PowerSheaf.tensorPowerModule L (n + m))).hom := (Category.assoc _ _ _).symm
    _ = 0 := by rw [hm, zero_comp]

/-- Numerators agreeing on the chart's part of `D(s)` agree everywhere on the
chart after applying a suitable global degree transition. -/
theorem affine_chart_power_equality
    (e : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj L) [IsIso e]
    (s : Line.Bundles.structureModule Y ⟶ L) (n : ℕ)
    (t t' : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj (TensorPower.PowerSheaf.tensorPowerModule L n))
    (ht : Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)).ι t =
      Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)).ι t') :
    ∃ m : ℕ, t ≫ (Scheme.Modules.pullback f).map (Power.SectionTransitions.powerSectionTransition s n m) =
      t' ≫ (Scheme.Modules.pullback f).map (Power.SectionTransitions.powerSectionTransition s n m) := by
  have hsub : Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)).ι (t - t') =
      Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)).ι t -
        Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)).ι t' :=
    pullbackSection_sub _ t t'
  obtain ⟨m, hm⟩ := affine_chart_power_annihilation f e s n (t - t')
    (hsub.trans (by rw [ht, sub_self]))
  exact ⟨m, sub_eq_zero.mp ((Preadditive.sub_comp t t' _).symm.trans hm)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictedPowerAnnihilation
