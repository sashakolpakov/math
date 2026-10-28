import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.BirationalCharts

/-! # Relative Isomorphism -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.RelativeIsomorphism.BundleCycles

noncomputable section

/-!
# LineBundleCycles: finite birational maps to the relative normalization are isomorphisms
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.Normalization.BundleCycles.RelativeNormalization OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationLocal.BundleCycles.RelativeNormalizationLocal

universe u
variable (Y : Scheme.{u}) [IsIntegral Y] (L : Type u) [Field L]
    [Algebra Y.functionField L] [Module.Finite Y.functionField L]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Relative.Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L) [IsFinite f]
    (hη : f (genericPoint X) = genericPoint (Relative.Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L))
    [IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη)]

include hη

theorem finiteBirational_relativeNormalization_isIso : IsIso f := by
  let V (z : Relative.Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L) : Y.Opens :=
    (Y.affineCover.f (Y.affineCover.idx (Relative.Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L z))).opensRange
  have hV (z : Relative.Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L) : IsAffineOpen (V z) :=
    isAffineOpen_opensRange (Y.affineCover.f _)
  have hzV (z : Relative.Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L) : Relative.Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L z ∈ V z :=
    Y.affineCover.covers (Relative.Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L z)
  let U (z : Relative.Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L) : (Relative.Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L).affineOpens :=
    ⟨Relative.Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L ⁻¹ᵁ V z, (hV z).preimage (Relative.Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L)⟩
  let nonemptyRelativeChart (z : Relative.Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L) : Nonempty (U z : (Relative.Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L).Opens) :=
    ⟨⟨z, hzV z⟩⟩
  have hcover : ⨆ z, (U z : (Relative.Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L).Opens) = ⊤ := by
    apply eq_top_iff.mpr
    intro z _
    exact Opens.mem_iSup.mpr ⟨z, hzV z⟩
  apply BirationalCharts.BundleCycles.finiteBirational_isIso_of_normal_cover f hη U hcover
  intro z
  let : Nonempty (V z) := ⟨⟨Relative.Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L z, hzV z⟩⟩
  exact Relative.NormalizationLocal.BundleCycles.RelativeNormalizationLocal.affineSections_integrallyClosed Y L (V z) (hV z)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.RelativeIsomorphism.BundleCycles
