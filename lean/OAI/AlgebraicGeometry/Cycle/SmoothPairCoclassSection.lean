/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicGeometry.Cycle.SmoothPairOpen
import OAI.AlgebraicTopology.Support.RelativeCohomologyEq

/-! # Smooth Pair Coclass Section -/

namespace OAI.AlgebraicGeometry.Cycle.SmoothPairCoclassSection.ComplexPoint

noncomputable section

open _root_.AlgebraicGeometry

/-!
# The global normalized smooth-support coclass section

Holomorphic normal charts supply local relative coclasses whose ambient overlap agreement
identifies their sheaf germs, and those germs vanish off the closed image because the
relative complexes do. Unique sheaf gluing then produces the global section, with its
complex normalization.
-/

open _root_.CategoryTheory Limits _root_.TopologicalSpace Opposite
open OAI.AlgebraicTopology.Singular
open scoped OAI.AlgebraicTopology.Support.RelativeCohomologySheaf.Singular
open _root_.TopCat.Presheaf

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]

/-- Let `i: Y → X` be a closed immersion of smooth complex schemes of respective dimensions `m` and
`d`, and put `S = i(Y(ℂ))` and `c = d-m`. For `z ∈ Y(ℂ)`, this is the source of a chosen
holomorphic chart near `i(z)` with coordinates in `ℂ^m × ℂ^c` in which `S` is the zero set of
the normal coordinate. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartOpen (z : ComplexPoint.Basic.ComplexSchemePoint Y) :
    Opens (ComplexPoint.Basic.ComplexSchemePoint X) :=
  ⟨(ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z).source,
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z).open_source⟩

theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.mem_smoothClosedSupportChartOpen (z : ComplexPoint.Basic.ComplexSchemePoint Y) :
    ComplexPoint.Basic.Point.map i z ∈ ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartOpen X Y i m d z :=
  ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart_mem_source X Y i m d z

/-- Let `i: Y → X` be a closed immersion of smooth complex schemes of dimensions `m,d`. Put `S =
i(Y(ℂ))` and `c = d-m`. This is the sheafification on `X(ℂ)` of the relative singular cohomology
presheaf `V ↦ H^{2c}(V,V \ S;ℚ)`, considered as abelian groups. -/
abbrev _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassSheaf : TopCat.Sheaf AddCommGrpCat
    (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) :=
  -- The support is `Y(ℂ) ⊆ X(ℂ)`, the image of the closed immersion `i`; the degree is twice
  -- the codimension of `Y` in `X`.
  𝓗_[Set.range (ComplexPoint.Basic.Point.map i)]^(2 * (d - m))(TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X); ℚ)

/-- Let `i: Y → X` be a closed immersion of smooth complex schemes of dimensions `m,d`. Put `S =
i(Y(ℂ))` and `c = d-m`. On the chosen normal chart at `i(z)`, with `z ∈ Y(ℂ)`, this is a section
of the sheafification of `V ↦ H^{2c}(V,V \ S;ℚ)`. It is obtained by pulling back the class in
`H^{2c}(ℂ^c,ℂ^c \ {0};ℚ)` evaluating to `1` on the complex orientation class along the normal
coordinate and sheafifying. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartSheafSection (z : ComplexPoint.Basic.ComplexSchemePoint Y) :
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassSheaf X Y i m d).presheaf.obj
      (op (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartOpen X Y i m d z)) :=
  (AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
    (Set.range (ComplexPoint.Basic.Point.map i)) (2 * (d - m))).app _
      (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartCoclass X Y i m d z
        (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartOpen X Y i m d z) (le_refl _))

/-- Let `i: Y → X` be a closed immersion of smooth complex schemes of dimensions `m,d`. Put `S =
i(Y(ℂ))` and `c = d-m`. For `z ∈ Y(ℂ)` and `x` in the chosen normal chart at `i(z)`, this is a
germ in the sheafification of `V ↦ H^{2c}(V,V \ S;ℚ)`. It is the germ at `x` of the pullback
along the normal coordinate of the class in `H^{2c}(ℂ^c,ℂ^c \ {0};ℚ)` evaluating to `1` on the
complex orientation class. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartCoclassGerm (z : ComplexPoint.Basic.ComplexSchemePoint Y)
    (x : ComplexPoint.Basic.ComplexSchemePoint X)
    (hx : x ∈ ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartOpen X Y i m d z) :
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassSheaf X Y i m d).presheaf.stalk x :=
  AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyGerm (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
    (Set.range (ComplexPoint.Basic.Point.map i)) (2 * (d - m))
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartOpen X Y i m d z) x hx
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartCoclass X Y i m d z
      (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartOpen X Y i m d z) (le_refl _))

set_option backward.isDefEq.respectTransparency false in
/-- The ambient overlap theorem proves equality of chart germs on support. -/
private theorem smoothClosedSupportChartCoclassGerm_eq
    (z z' : ComplexPoint.Basic.ComplexSchemePoint Y) (x : ComplexPoint.Basic.ComplexSchemePoint X)
    (hxS : x ∈ Set.range (ComplexPoint.Basic.Point.map i))
    (hx : x ∈ ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartOpen X Y i m d z)
    (hx' : x ∈ ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartOpen X Y i m d z') :
    ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartCoclassGerm X Y i m d z x hx =
      ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartCoclassGerm X Y i m d z' x hx' := by
  obtain ⟨W, hW, hW', hxW, heq⟩ := ComplexPoint.Basic.ComplexSchemePoint.exists_open_smoothClosedSupportChartCoclass_eq
    X Y i m d z z' x hxS hx hx'
  apply AlgebraicTopology.Support.RelativeCohomologyEq.Singular.supportRelativeCohomologyGerm_eq_of_restrict_eq
    (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) (Set.range (ComplexPoint.Basic.Point.map i)) (2 * (d - m))
    (U := ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartOpen X Y i m d z)
    (V := ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartOpen X Y i m d z')
    hW hW' x hxW
  simpa only [ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartCoclass_restrict] using heq

/-- Away from the closed image, the chart coclass germ is zero. -/
private theorem smoothClosedSupportChartCoclassGerm_eq_zero
    (z : ComplexPoint.Basic.ComplexSchemePoint Y) (x : ComplexPoint.Basic.ComplexSchemePoint X)
    (hx : x ∈ ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartOpen X Y i m d z)
    (hxS : x ∉ Set.range (ComplexPoint.Basic.Point.map i)) :
    ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartCoclassGerm X Y i m d z x hx = 0 :=
  AlgebraicTopology.Support.RelativeCohomologyEq.Singular.supportRelativeCohomologyGerm_eq_zero_of_not_mem
    (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) (Set.range (ComplexPoint.Basic.Point.map i)) (2 * (d - m))
    (ComplexPoint.Basic.ComplexSchemePoint.isClosed_range_map_of_closedImmersion i)
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartOpen X Y i m d z) x hx hxS
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartCoclass X Y i m d z
      (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartOpen X Y i m d z) (le_refl _))

open scoped Classical in
/-- Let `i: Y → X` be a closed immersion of smooth complex schemes of dimensions `m,d`. Put `S =
i(Y(ℂ))` and `c = d-m`. This element of the stalk at `x` of the sheafification of `V ↦
H^{2c}(V,V \ S;ℚ)` is zero off `S`. On `S`, it is the germ of the pullback, in a chosen normal
chart at `x`, of the class in `H^{2c}(ℂ^c,ℂ^c \ {0};ℚ)` evaluating to `1` on the complex
orientation class. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassStalk (x : ComplexPoint.Basic.ComplexSchemePoint X) :
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassSheaf X Y i m d).presheaf.stalk x :=
  if hxS : x ∈ Set.range (ComplexPoint.Basic.Point.map i) then
    ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartCoclassGerm X Y i m d hxS.choose x
      (by simpa only [hxS.choose_spec] using
        ComplexPoint.Basic.ComplexSchemePoint.mem_smoothClosedSupportChartOpen X Y i m d hxS.choose)
  else 0

/-- The normalized germ family agrees with every chart, including at points outside the
support. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassStalk_eq_chartGerm
    (z : ComplexPoint.Basic.ComplexSchemePoint Y) (x : ComplexPoint.Basic.ComplexSchemePoint X)
    (hx : x ∈ ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartOpen X Y i m d z) :
    ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassStalk X Y i m d x =
      ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartCoclassGerm X Y i m d z x hx := by
  by_cases hxS : x ∈ Set.range (ComplexPoint.Basic.Point.map i)
  · rw [ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassStalk, dite_eq_left hxS]
    exact smoothClosedSupportChartCoclassGerm_eq X Y i m d
      hxS.choose z x hxS _ hx
  · rw [ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassStalk, dite_eq_right hxS]
    exact (smoothClosedSupportChartCoclassGerm_eq_zero X Y i m d z x hx hxS).symm

@[simp] theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassStalk_eq_zero
    (x : ComplexPoint.Basic.ComplexSchemePoint X) (hxS : x ∉ Set.range (ComplexPoint.Basic.Point.map i)) :
    ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassStalk X Y i m d x = 0 := by
  rw [ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassStalk, dite_eq_right hxS]

/-- The charts and the open support complement prove local representability
of the entire normalized stalk family. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassStalk_locallyRepresentable :
    ∀ x : ComplexPoint.Basic.ComplexSchemePoint X,
      ∃ (U : Opens (ComplexPoint.Basic.ComplexSchemePoint X)) (_ : x ∈ U)
        (s : (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassSheaf X Y i m d).presheaf.obj (op U)),
        ∀ (y : ComplexPoint.Basic.ComplexSchemePoint X) (hy : y ∈ U),
          (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassSheaf X Y i m d).presheaf.germ U y hy s =
            ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassStalk X Y i m d y := by
  intro x
  by_cases hxS : x ∈ Set.range (ComplexPoint.Basic.Point.map i)
  · obtain ⟨z, rfl⟩ := hxS
    refine ⟨ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartOpen X Y i m d z,
      ComplexPoint.Basic.ComplexSchemePoint.mem_smoothClosedSupportChartOpen X Y i m d z,
      ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportChartSheafSection X Y i m d z, ?_⟩
    exact fun y hy ↦ (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassStalk_eq_chartGerm X Y i m d z y hy).symm
  · let U : Opens (ComplexPoint.Basic.ComplexSchemePoint X) :=
      ⟨(Set.range (ComplexPoint.Basic.Point.map i))ᶜ, (ComplexPoint.Basic.ComplexSchemePoint.isClosed_range_map_of_closedImmersion i).isOpen_compl⟩
    refine ⟨U, hxS, 0, ?_⟩
    intro y hy
    rw [map_zero, ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassStalk_eq_zero X Y i m d y hy]

/-- Let `i: Y → X` be a closed immersion of smooth complex schemes of dimensions `m,d`. Put `S =
i(Y(ℂ))` and `c = d-m`. This global section of the sheafification of `V ↦ H^{2c}(V,V \ S;ℚ)`
glues the zero section off `S` with pullbacks in normal charts of the class in `H^{2c}(ℂ^c,ℂ^c \
{0};ℚ)` evaluating to `1` on the complex orientation class. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassSection :
    -- A global section of `𝓗^{2(d-m)}_{Y(ℂ)}` on `X(ℂ)`.
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassSheaf X Y i m d).presheaf.obj
      -- All of `X(ℂ)`.
      (op ⊤) :=
  AlgebraicTopology.Sheaf.MapOfLocalStalks.TopCat.sectionOfLocallyRepresentable _
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassStalk X Y i m d)
    (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportCoclassStalk_locallyRepresentable X Y i m d)

end

end OAI.AlgebraicGeometry.Cycle.SmoothPairCoclassSection.ComplexPoint
