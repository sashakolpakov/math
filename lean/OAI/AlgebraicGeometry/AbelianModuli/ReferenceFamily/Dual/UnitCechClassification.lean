import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitCechClasses

/-! # Unit Cech Classification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitCechClassification

noncomputable section

section

/-! A zero infinitesimal cohomology class yields actual normalized
transition gauges on the same open cover. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}} (R : TopCat.Sheaf CommRingCat.{0} X)
    {I : Type} (U : I → Opens X)

local instance dualUnitClassGroup : AddCommGroup (CategoryTheory.Sheaf.H (UnitCechClasses.ringAdditiveSheaf R) 1) :=
  Cech.Add.cechClassAddCommGroup (UnitCechClasses.ringAdditiveSheaf R) 1

theorem dualUnitCechClass_zero_gauge (hU : iSup U = ⊤) (u : UnitCechCoefficients.DualUnitCechCoefficients R.obj U)
    (hu : UnitCechCoefficients.DualUnitCechNormalized R.obj U u) (hc : UnitCechCoefficients.DualUnitCechCocycle R.obj U u)
    (hz : UnitCechClasses.dualUnitCechClass R U hU u hu hc = 0) :
    ∃ g : ∀ i, (DualNumber (R.obj.obj (op (U i))))ˣ,
      (∀ i, (g i).val.fst = 1) ∧ ∀ a : Fin 2 → I, u a =
        UnitCechCoefficients.dualCechRestrict R.obj (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1) (g (a 1)) /
        UnitCechCoefficients.dualCechRestrict R.obj (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0) (g (a 0)) := by
  let F := UnitCechClasses.ringAdditiveSheaf R
  obtain ⟨b, hb⟩ := Cech.Add.cech_one_boundary_of_sheaf_class_zero U F hU
    (UnitCechCoefficients.dualUnitCechAdditive R.obj U u) (UnitCechCoefficients.dualUnitCechAdditive_closed R.obj U u hu hc) hz
  obtain ⟨s, hs⟩ := Cech.Add.cech_zero_eq_localSections U F b
  let g (i : I) : (DualNumber (R.obj.obj (op (U i))))ˣ := UnitCoordinates.normalizedDualUnit (s i)
  have hg (i : I) : (g i).val.fst = 1 := rfl
  refine ⟨g, hg, ?_⟩
  intro a
  apply UnitCoordinates.normalizedDualUnits_ext _ _ (hu a)
    (UnitCoordinates.dualUnit_fst_div _ _ (UnitCechCoefficients.dualCechRestrict_fst R.obj _ _ (hg _))
      (UnitCechCoefficients.dualCechRestrict_fst R.obj _ _ (hg _)))
  rw [UnitCoordinates.dualUnit_snd_div _ _ (UnitCechCoefficients.dualCechRestrict_fst R.obj _ _ (hg _))
    (UnitCechCoefficients.dualCechRestrict_fst R.obj _ _ (hg _)), UnitCechCoefficients.dualCechRestrict_snd, UnitCechCoefficients.dualCechRestrict_snd]
  have h := congrFun ((congrArg (DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F.obj U 0) hs).trans hb) a
  erw [DivisorClass.Chern.Cech.LocalSections.abelianCechLocalSections_delta] at h
  exact h.symm

end

/-! Equality of the actual infinitesimal sheaf classes is equivalent
to a normalized multiplicative change of frame on the original cover. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}} (R : TopCat.Sheaf CommRingCat.{0} X)
    {I : Type} (U : I → Opens X)

theorem dualUnitCechClass_eq_iff_gauge (hU : iSup U = ⊤)
    (u v : UnitCechCoefficients.DualUnitCechCoefficients R.obj U)
    (hu : UnitCechCoefficients.DualUnitCechNormalized R.obj U u) (hv : UnitCechCoefficients.DualUnitCechNormalized R.obj U v)
    (hcu : UnitCechCoefficients.DualUnitCechCocycle R.obj U u) (hcv : UnitCechCoefficients.DualUnitCechCocycle R.obj U v) :
    UnitCechClasses.dualUnitCechClass R U hU v hv hcv = UnitCechClasses.dualUnitCechClass R U hU u hu hcu ↔
    ∃ g : ∀ i, (DualNumber (R.obj.obj (op (U i))))ˣ,
      (∀ i, (g i).val.fst = 1) ∧ ∀ a : Fin 2 → I, v a = u a *
        UnitCechCoefficients.dualCechRestrict R.obj (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1) (g (a 1)) /
        UnitCechCoefficients.dualCechRestrict R.obj (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0) (g (a 0)) := by
  constructor
  · intro he
    let F := UnitCechClasses.ringAdditiveSheaf R
    obtain ⟨b, hb⟩ := Cech.Add.cech_one_difference_boundary U F hU
      (UnitCechCoefficients.dualUnitCechAdditive R.obj U v) (UnitCechCoefficients.dualUnitCechAdditive R.obj U u)
      (UnitCechCoefficients.dualUnitCechAdditive_closed R.obj U v hv hcv)
      (UnitCechCoefficients.dualUnitCechAdditive_closed R.obj U u hu hcu) he
    obtain ⟨s, hs⟩ := Cech.Add.cech_zero_eq_localSections U F b
    let g (i : I) : (DualNumber (R.obj.obj (op (U i))))ˣ := UnitCoordinates.normalizedDualUnit (s i)
    have hg (i : I) : (g i).val.fst = 1 := rfl
    refine ⟨g, hg, ?_⟩
    intro a
    have h0 := UnitCechCoefficients.dualCechRestrict_fst R.obj (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0) (g (a 0)) (hg _)
    have h1 := UnitCechCoefficients.dualCechRestrict_fst R.obj (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1) (g (a 1)) (hg _)
    have hup : (u a * UnitCechCoefficients.dualCechRestrict R.obj (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1) (g (a 1))).val.fst = 1 := by
      change (u a).val.fst * (UnitCechCoefficients.dualCechRestrict R.obj _ _).val.fst = 1
      rw [hu a, h1, one_mul]
    apply UnitCoordinates.normalizedDualUnits_ext _ _ (hv a) (UnitCoordinates.dualUnit_fst_div _ _ hup h0)
    rw [UnitCoordinates.dualUnit_snd_gauge _ _ _ (hu a) h0 h1, UnitCechCoefficients.dualCechRestrict_snd, UnitCechCoefficients.dualCechRestrict_snd]
    have h := congrFun ((congrArg (DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F.obj U 0) hs).trans hb) a
    erw [DivisorClass.Chern.Cech.LocalSections.abelianCechLocalSections_delta] at h
    change R.obj.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1)).op (s (a 1)) -
        R.obj.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0)).op (s (a 0)) =
          (v a).val.snd - (u a).val.snd at h
    change (v a).val.snd = (u a).val.snd +
      R.obj.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1)).op (s (a 1)) -
      R.obj.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0)).op (s (a 0))
    rw [add_sub_assoc, h]
    abel
  · rintro ⟨g, hg, he⟩
    exact UnitCechClasses.dualUnitCechClass_gauge R U hU u v hu hv hcu hcv g hg he

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitCechClassification
