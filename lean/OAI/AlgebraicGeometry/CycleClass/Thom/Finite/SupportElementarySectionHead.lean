import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SupportRegularHead
import OAI.AlgebraicGeometry.CycleClass.Thom.StalkTailSection
import OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkNonvanishing
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.NormalizationNeighborhood

/-! # Support Elementary Section Head -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SupportElementarySectionHead.Constructions

noncomputable section

section

/-! A genuine regular section head can be chosen simultaneously for
finitely many original parent supports through a point. The complete
section ideal is unchanged on the smaller open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace RingTheory.Sequence

open OAI.AlgebraicGeometry.CycleClass.Thom.SupportStalkModule.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkTailSection.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkNonvanishing.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.NormalizationNeighborhood.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (x : V.carrier)
  {ι : Type} [Fintype ι] (D : ι → Geometric.DimensionCycles.DimensionCycleSupport V p)
  (hxD : ∀ i, x ∈ ((D i).val : Set V.carrier))
  (B : V.carrier.Opens) (hxB : x ∈ B)
  (r : Γ(V.carrier, B)) (rs : List Γ(V.carrier, B))

local notation "R" => V.carrier.presheaf.stalk x
local notation "gB" => V.carrier.presheaf.germ B x hxB

theorem exists_section_head
    (hr : IsWeaklyRegular R (gB r :: rs.map gB))
    (hm : ∀ a ∈ gB r :: rs.map gB, a ∈ IsLocalRing.maximalIdeal R)
    (hI : ∀ i, ¬ Ideal.ofList (gB r :: rs.map gB) ≤
      RingHom.ker (SupportStalkModule.Constructions.supportStalkMap V.carrier (D i).val x (hxD i)).hom) :
    ∃ C : V.carrier.Opens, ∃ hCB : C ≤ B, ∃ hxC : x ∈ C, ∃ s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase C).left, ⊤),
      Ideal.ofList (C.topIso.hom s :: rs.map (V.carrier.presheaf.map (homOfLE hCB).op)) =
        Ideal.ofList ((r :: rs).map (V.carrier.presheaf.map (homOfLE hCB).op)) ∧
      IsWeaklyRegular R (V.carrier.presheaf.germ C x hxC (C.topIso.hom s) :: rs.map gB) ∧
      (∀ a ∈ V.carrier.presheaf.germ C x hxC (C.topIso.hom s) :: rs.map gB,
        a ∈ IsLocalRing.maximalIdeal R) ∧
      ∀ i, letI := Affine.NormalizationNeighborhood.Constructions.normalizationBase_nonempty (D i) C x (hxD i) hxC
        Affine.SectionFunction.Constructions.parentSectionFunction (D i) C s ≠ 0 := by
  let E : ι → V.presentation.DimensionCycleSupport p := fun i =>
    ⟨(D i).val, (Integral.ProductSupport.Constructions.integralPresentation_supportCodimension V (D i).val).trans (D i).property⟩
  obtain ⟨t, ht, _, hreg, hmax, hn⟩ :=
    SupportRegularHead.Constructions.exists_regular_head V.presentation p x E hxD (gB r) (rs.map gB) hr hm hI
  obtain ⟨C, hCB, hxC, a, he, hga⟩ := StalkTailSection.Constructions.exists_head_adjustment V.carrier x B hxB r rs t ht
  let s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase C).left, ⊤) := C.topIso.inv a
  have htop : C.topIso.hom s = a := ConcreteCategory.congr_hom C.topIso.inv_hom_id a
  have hg : V.carrier.presheaf.germ C x hxC (C.topIso.hom s) = gB r + t :=
    (congrArg (V.carrier.presheaf.germ C x hxC) htop).trans hga
  refine ⟨C, hCB, hxC, s, ?_, ?_, ?_, ?_⟩
  · rw [htop]
    exact he
  · rw [hg]
    exact hreg
  · rw [hg]
    exact hmax
  · intro i
    let := Affine.NormalizationNeighborhood.Constructions.normalizationBase_nonempty (D i) C x (hxD i) hxC
    apply (Section.StalkNonvanishing.Constructions.parentFunction_ne_zero_iff (D i) C s x (hxD i) hxC).mpr
    rw [hg]
    exact hn i

end

/-! Simultaneous regular head selection retains its actual elementary
section change, so the resulting normal-coordinate map can be compared
by the already constructed relative homotopy. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace RingTheory.Sequence

open OAI.AlgebraicGeometry.CycleClass.Thom.SupportStalkModule.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkTailSection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Regular.SequenceTailChange.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.NormalizationNeighborhood.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkNonvanishing.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (x : V.carrier)
  {ι : Type} [Fintype ι] (D : ι → Geometric.DimensionCycles.DimensionCycleSupport V p)
  (hxD : ∀ i, x ∈ ((D i).val : Set V.carrier))
  (B : V.carrier.Opens) (hxB : x ∈ B)
  (r : Γ(V.carrier, B)) (rs : List Γ(V.carrier, B))

local notation "R" => V.carrier.presheaf.stalk x
local notation "gB" => V.carrier.presheaf.germ B x hxB

theorem exists_elementary_section_head
    (hr : IsWeaklyRegular R (gB r :: rs.map gB))
    (hm : ∀ a ∈ gB r :: rs.map gB, a ∈ IsLocalRing.maximalIdeal R)
    (hI : ∀ i, ¬ Ideal.ofList (gB r :: rs.map gB) ≤
      RingHom.ker (SupportStalkModule.Constructions.supportStalkMap V.carrier (D i).val x (hxD i)).hom) :
    ∃ C : V.carrier.Opens, ∃ hCB : C ≤ B, ∃ hxC : x ∈ C, ∃ s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase C).left, ⊤),
      C.topIso.hom s - V.carrier.presheaf.map (homOfLE hCB).op r ∈
        Ideal.ofList (rs.map (V.carrier.presheaf.map (homOfLE hCB).op)) ∧
      Ideal.ofList (C.topIso.hom s :: rs.map (V.carrier.presheaf.map (homOfLE hCB).op)) =
        Ideal.ofList ((r :: rs).map (V.carrier.presheaf.map (homOfLE hCB).op)) ∧
      IsWeaklyRegular R (V.carrier.presheaf.germ C x hxC (C.topIso.hom s) :: rs.map gB) ∧
      (∀ a ∈ V.carrier.presheaf.germ C x hxC (C.topIso.hom s) :: rs.map gB,
        a ∈ IsLocalRing.maximalIdeal R) ∧
      ∀ i, letI := Affine.NormalizationNeighborhood.Constructions.normalizationBase_nonempty (D i) C x (hxD i) hxC
        Affine.SectionFunction.Constructions.parentSectionFunction (D i) C s ≠ 0 := by
  let E : ι → V.presentation.DimensionCycleSupport p := fun i =>
    ⟨(D i).val, (Integral.ProductSupport.Constructions.integralPresentation_supportCodimension V (D i).val).trans (D i).property⟩
  obtain ⟨t, ht, _, hreg, hmax, hn⟩ :=
    SupportRegularHead.Constructions.exists_regular_head V.presentation p x E hxD (gB r) (rs.map gB) hr hm hI
  obtain ⟨C, hCB, hxC, u, hu, hgu⟩ := StalkTailSection.Constructions.exists_tail_section V.carrier x B hxB rs t ht
  let ρ := V.carrier.presheaf.map (homOfLE hCB).op
  let a := ρ r + u
  let s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase C).left, ⊤) := C.topIso.inv a
  have htop : C.topIso.hom s = a := ConcreteCategory.congr_hom C.topIso.inv_hom_id a
  have hg : V.carrier.presheaf.germ C x hxC (C.topIso.hom s) = gB r + t := by
    rw [htop]
    change V.carrier.presheaf.germ C x hxC (ρ r + u) = _
    rw [map_add, hgu]
    exact congrArg (fun z => z + t) (V.carrier.presheaf.germ_res_apply (homOfLE hCB) x hxC r)
  refine ⟨C, hCB, hxC, s, ?_, ?_, ?_, ?_, ?_⟩
  · rw [htop]
    change ρ r + u - ρ r ∈ Ideal.ofList (rs.map ρ)
    rwa [add_sub_cancel_left]
  · rw [htop]
    exact Regular.SequenceTailChange.Constructions.ofList_add_tail (ρ r) u (rs.map ρ) hu
  · rw [hg]
    exact hreg
  · rw [hg]
    exact hmax
  · intro i
    let := Affine.NormalizationNeighborhood.Constructions.normalizationBase_nonempty (D i) C x (hxD i) hxC
    apply (Section.StalkNonvanishing.Constructions.parentFunction_ne_zero_iff (D i) C s x (hxD i) hxC).mpr
    rw [hg]
    exact hn i

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SupportElementarySectionHead.Constructions
