import OAI.NumberTheory.PadicHodge.GeometricComparison.ResolvedHypercohomologyEquiv
import OAI.NumberTheory.PadicHodge.GeometricComparison.PackagedResolved

/-! # Resolved Normalization -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.ResolvedNormalization.IntrinsicResolvedNormalization

noncomputable section

/-! The native section resolution comparison is the proved coefficient-Hom comparison under the canonical section equivalence. -/

open _root_.CategoryTheory Limits Abelian

variable (R : Type) [CommRing R] (X : TopCat.{0})

local instance : HasExt.{1} (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R)) := HasExt.standard _
local instance : HasDerivedCategory.{1} (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R)) := HasDerivedCategory.standard _

theorem equiv_apply {K L : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R)) ℤ}
    (f : K ⟶ L) [QuasiIso f] (b : ℤ) [L.IsStrictlyGE b]
    (hL : ∀ p q, Subsingleton (Ext.{1} (ConstantSheaf.ConstantSheafSections.coefficient R X) (L.X p) (q + 1)))
    (n : ℤ) (x : (Section.Hypercohomology.SectionHypercohomology.sectionComplex R X L).homology n) :
    ResolvedHypercohomologyEquiv.ResolvedHypercohomology.equiv R X f b hL n x =
      PackagedResolved.PackagedResolvedComparison.equivWithSystem.{1, 0, 1, 1} R
        (ConstantSheaf.ConstantSheafSections.coefficient R X) (Section.Hypercohomology.SectionHypercohomology.comparisonSystem R X) f b hL n
        (Section.Hypercohomology.SectionHypercohomology.homologyEquiv R X L n x) := by
  let d := DerivedQuasiHom.DerivedQuasiIsoHom.equiv R (ConstantSheaf.ConstantSheafSections.coefficient R X) f n
  let e := Section.Hypercohomology.SectionHypercohomology.equiv R X L b hL n
  let g := Section.Hypercohomology.SectionHypercohomology.derivedEquiv R X L b hL n
  let z := Section.Hypercohomology.SectionHypercohomology.homologyEquiv R X L n x
  have h₁ : (e.trans d) x = d (e x) := LinearEquiv.trans_apply (e₁₂ := e) (e₂₃ := d) x
  have h₂ : d (e x) = d (g z) := congrArg d (Section.Hypercohomology.SectionHypercohomology.equiv_apply R X L b hL n x)
  have h₃ : (g.trans d) z = d (g z) := LinearEquiv.trans_apply (e₁₂ := g) (e₂₃ := d) z
  exact h₁.trans (h₂.trans h₃.symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.ResolvedNormalization.IntrinsicResolvedNormalization
