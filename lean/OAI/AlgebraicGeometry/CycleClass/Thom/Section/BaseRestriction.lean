import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation

/-! # Base Restriction -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Section.BaseRestriction.Constructions

/-! Restricting the affine base and its actual section preserves the
original parent rational function. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B C : V.carrier.Opens) (hCB : C ≤ B)
  [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)]
  [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ C)]

local instance : Nonempty (D.inclusion ⁻¹ᵁ B) := by
  obtain ⟨x⟩ := ‹Nonempty ((normalizationToAmbient V D.val).left ⁻¹ᵁ B)›
  exact ⟨⟨Normalization.Scheme.Constructions.normalizationMap D.scheme x.val, x.property⟩⟩
local instance : Nonempty (D.inclusion ⁻¹ᵁ C) := by
  obtain ⟨x⟩ := ‹Nonempty ((normalizationToAmbient V D.val).left ⁻¹ᵁ C)›
  exact ⟨⟨Normalization.Scheme.Constructions.normalizationMap D.scheme x.val, x.property⟩⟩

omit D [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)]
  [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ C)] in
theorem topIso_sectionRestriction (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) :
    C.topIso.hom ((V.carrier.homOfLE hCB).appTop s) =
      V.carrier.presheaf.map (homOfLE hCB).op (B.topIso.hom s) := by
  apply (ConcreteCategory.bijective_of_isIso C.topIso.inv).injective
  have h := ConcreteCategory.congr_hom (Scheme.SectionEvaluation.Constructions.topIso_inv_restrict V.toOver hCB) (B.topIso.hom s)
  change C.topIso.inv (V.carrier.presheaf.map (homOfLE hCB).op (B.topIso.hom s)) =
    (V.carrier.homOfLE hCB).appTop (B.topIso.inv (B.topIso.hom s)) at h
  simpa only [Iso.hom_inv_id_apply] using h.symm

 theorem parentSectionFunction_restrict (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) :
    Affine.SectionFunction.Constructions.parentSectionFunction D C ((V.carrier.homOfLE hCB).appTop s) = Affine.SectionFunction.Constructions.parentSectionFunction D B s := by
  unfold Affine.SectionFunction.Constructions.parentSectionFunction
  rw [topIso_sectionRestriction B C hCB s]
  have hn := ConcreteCategory.congr_hom (D.inclusion.naturality (homOfLE hCB).op) (B.topIso.hom s)
  have hp : D.inclusion ⁻¹ᵁ C ≤ D.inclusion ⁻¹ᵁ B := fun _ hx => hCB hx
  exact (congrArg (D.scheme.germToFunctionField (D.inclusion ⁻¹ᵁ C)) hn).trans
    (RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative.germ_restrict hp (D.inclusion.app B (B.topIso.hom s)))

end AlgebraicGeometry.CycleClass.Thom.Section.BaseRestriction.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.Section.BaseRestriction.Constructions.HeadDifference

/-! An elementary head difference in the ambient open's section ring
is the same genuine tail-ideal difference in the global sections of
the smaller open scheme, as required by the vector homotopy. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Section.BaseRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (B C : V.carrier.Opens) (hCB : C ≤ B)

abbrev restrictSection (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase C).left, ⊤) :=
  (V.carrier.homOfLE hCB).appTop s

theorem globalSection_restrict (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) :
    C.topIso.inv (V.carrier.presheaf.map (homOfLE hCB).op (B.topIso.hom s)) =
      restrictSection V B C hCB s := by
  apply (ConcreteCategory.bijective_of_isIso C.topIso.hom).injective
  rw [Iso.inv_hom_id_apply, topIso_sectionRestriction B C hCB s]

theorem head_difference_mem (r : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (rs : List Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))
    (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase C).left, ⊤))
    (h : C.topIso.hom s - V.carrier.presheaf.map (homOfLE hCB).op (B.topIso.hom r) ∈
      Ideal.ofList ((rs.map B.topIso.hom).map (V.carrier.presheaf.map (homOfLE hCB).op))) :
    s - restrictSection V B C hCB r ∈ Ideal.ofList (rs.map (restrictSection V B C hCB)) := by
  have hd := Ideal.mem_map_of_mem C.topIso.inv.hom h
  have htail : (((rs.map B.topIso.hom).map (V.carrier.presheaf.map (homOfLE hCB).op)).map C.topIso.inv) =
      rs.map (restrictSection V B C hCB) := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro a _
    exact globalSection_restrict V B C hCB a
  have hval : C.topIso.inv (C.topIso.hom s - V.carrier.presheaf.map (homOfLE hCB).op (B.topIso.hom r)) =
      s - restrictSection V B C hCB r := by
    rw [map_sub, Iso.hom_inv_id_apply, globalSection_restrict]
  rw [Ideal.map_ofList, htail, hval] at hd
  exact hd

end AlgebraicGeometry.CycleClass.Thom.Section.BaseRestriction.Constructions.HeadDifference

end

end OAI
