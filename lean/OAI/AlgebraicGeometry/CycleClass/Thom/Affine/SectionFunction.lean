import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SourceFieldMap
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.SectionBasic

/-! # Section Function -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions

/-! The rational function constructed on the original cycle is exactly
the germ of the ambient section restricted to that cycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SourceFieldMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenFunctionField.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.SectionBasic.Constructions.Pullback

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B : V.carrier.Opens) [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)]

local instance supportOpen_nonempty : Nonempty (D.inclusion ⁻¹ᵁ B) := by
  obtain ⟨x⟩ := ‹Nonempty ((normalizationToAmbient V D.val).left ⁻¹ᵁ B)›
  exact ⟨⟨Normalization.Scheme.Constructions.normalizationMap D.scheme x.val, x.property⟩⟩

local instance : Nonempty (⊤ : (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left.Opens) :=
  ⟨⟨genericPoint (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left, Opens.mem_top _⟩⟩

def parentSectionFunction (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) : D.scheme.functionField :=
  D.scheme.germToFunctionField (D.inclusion ⁻¹ᵁ B) (D.inclusion.app B (B.topIso.hom s))

variable (hB : B ≤ Normalization.AmbientMap.Constructions.ambientOpen V D.val)

omit [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)] in
theorem sourceToSupport_affine_square :
    Normalization.SourceFieldMap.Constructions.sourceToSupport V D.val (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB) ≫ D.inclusion =
      (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineMap D B).left ≫ B.ι :=
  (Normalization.SourceFieldMap.Constructions.sourceToSupport_ambient V D.val (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB)).trans
    (congrArg Over.Hom.left (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth_ambient D B hB))

omit [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)] in
theorem sourceToSupport_preimage_base : (⊤ : (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left.Opens) ≤
    Normalization.SourceFieldMap.Constructions.sourceToSupport V D.val (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB) ⁻¹ᵁ (D.inclusion ⁻¹ᵁ B) := by
  intro x _
  have h := congrArg (fun m : (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left ⟶ V.carrier => m x)
    (sourceToSupport_affine_square D B hB)
  change (Normalization.SourceFieldMap.Constructions.sourceToSupport V D.val (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB) ≫ D.inclusion) x ∈ B
  exact (congrArg (fun y : V.carrier => y ∈ B) h).mpr ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineMap D B).left x).property

omit [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)] in
theorem sourceToSupport_section_pullback (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) :
    (Normalization.SourceFieldMap.Constructions.sourceToSupport V D.val (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB)).appLE (D.inclusion ⁻¹ᵁ B) ⊤
      (sourceToSupport_preimage_base D B hB) (D.inclusion.app B (B.topIso.hom s)) =
      (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineMap D B).left.appTop s := by
  let n := Normalization.SourceFieldMap.Constructions.sourceToSupport V D.val (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB)
  have hpre : (⊤ : (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left.Opens) ≤ (n ≫ D.inclusion) ⁻¹ᵁ B :=
    sourceToSupport_preimage_base D B hB
  have he := Open.SectionBasic.Constructions.Pullback.appLE_open_factor_apply B (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineMap D B).left (n ≫ D.inclusion)
    (sourceToSupport_affine_square D B hB).symm hpre s
  rw [Scheme.Hom.comp_appLE] at he
  exact he

 theorem originalFunction_eq_parentSectionFunction (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) :
    Normalization.OpenFunctionField.Constructions.originalFunction V D.val (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB)
      ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left.germToFunctionField ⊤ ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineMap D B).left.appTop s)) =
    parentSectionFunction D B s := by
  rw [← sourceToSupport_section_pullback D B hB s]
  exact Normalization.SourceFieldMap.Constructions.originalFunction_germ_appLE V D.val (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB) (D.inclusion ⁻¹ᵁ B)
    (sourceToSupport_preimage_base D B hB) (D.inclusion.app B (B.topIso.hom s))

end AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions.Nonzero

/-! Nonvanishing of the original restricted section is equivalent to
nonvanishing of its actual affine normalization pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenFunctionField.Constructions

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B : V.carrier.Opens) (hB : B ≤ Normalization.AmbientMap.Constructions.ambientOpen V D.val)
  [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)]

local instance : Nonempty (⊤ : (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left.Opens) :=
  ⟨⟨genericPoint (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left, Opens.mem_top _⟩⟩

include hB in
theorem sourceSection_germ_ne_zero (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (hs : parentSectionFunction D B s ≠ 0) :
    (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left.germToFunctionField ⊤ ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineMap D B).left.appTop s) ≠ 0 := by
  intro hz
  have h := originalFunction_eq_parentSectionFunction D B hB s
  rw [hz, Normalization.OpenFunctionField.Constructions.originalFunction, map_zero] at h
  exact hs h.symm

end AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions.Nonzero

end

end OAI
