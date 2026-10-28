import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.Hypercohomology
import OAI.NumberTheory.PadicHodge.GeometricComparison.DerivedQuasiIsoNaturality

/-! # Resolved Hypercohomology Equiv -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ResolvedHypercohomologyEquiv.ResolvedHypercohomology

noncomputable section

/-! An actual acyclic resolution computes coefficient hypercohomology naturally on commuting squares. -/

open _root_.CategoryTheory Abelian

variable (R : Type) [CommRing R] (X : TopCat.{0})

local notation "V" => OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantSheaf.ConstantSheafSections.Sheaves R X
local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantSheaf.ConstantSheafSections.coefficient R X

local instance : HasExt.{1} V := HasExt.standard _
local instance : HasDerivedCategory.{1} V := HasDerivedCategory.standard _

def equiv {K L : CochainComplex V ℤ} (f : K ⟶ L) [QuasiIso f]
    (c : ℤ) [L.IsStrictlyGE c]
    (hL : ∀ p q, Subsingleton (Ext.{1} A (L.X p) (q + 1))) (n : ℤ) :
    (Section.Hypercohomology.SectionHypercohomology.sectionComplex R X L).homology n ≃ₗ[R]
      ((DerivedCategory.singleFunctor V 0).obj A ⟶ (DerivedCategory.Q.obj K)⟦n⟧) :=
  (Section.Hypercohomology.SectionHypercohomology.equiv R X L c hL n).trans (DerivedQuasiHom.DerivedQuasiIsoHom.equiv R A f n)

theorem naturality {K L K' L' : CochainComplex V ℤ} (f : K ⟶ L) (g : K' ⟶ L')
    [QuasiIso f] [QuasiIso g] (a : K ⟶ K') (b : L ⟶ L') (h : f ≫ b = a ≫ g)
    (c d : ℤ) [L.IsStrictlyGE c] [L'.IsStrictlyGE d]
    (hL : ∀ p q, Subsingleton (Ext.{1} A (L.X p) (q + 1)))
    (hL' : ∀ p q, Subsingleton (Ext.{1} A (L'.X p) (q + 1))) (n : ℤ)
    (x : (Section.Hypercohomology.SectionHypercohomology.sectionComplex R X L).homology n) :
    equiv R X g d hL' n (HomologicalComplex.homologyMap
      (((Section.Hypercohomology.SectionHypercohomology.sections R X).mapHomologicalComplex (.up ℤ)).map b) n x) =
      equiv R X f c hL n x ≫ (DerivedCategory.Q.map a)⟦n⟧' := by
  exact (congrArg (DerivedQuasiHom.DerivedQuasiIsoHom.equiv R A g n)
    (Section.Hypercohomology.SectionHypercohomology.naturality R X c d hL hL' b n x)).trans
      (DerivedQuasiIsoNaturality.DerivedQuasiIsoHom.naturality R A f g a b h n
        (Section.Hypercohomology.SectionHypercohomology.equiv R X L c hL n x))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ResolvedHypercohomologyEquiv.ResolvedHypercohomology
