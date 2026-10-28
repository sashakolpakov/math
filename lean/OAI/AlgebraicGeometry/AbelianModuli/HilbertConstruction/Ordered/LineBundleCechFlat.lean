import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.BaseLineBundleSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechComplex
import Mathlib.LinearAlgebra.DFinsupp

/-! # Line Bundle Cech Flat -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.LineBundleCechFlat

noncomputable section

/-! Every term of a finite affine ordered Cech complex of a line bundle is flat over a flat affine base. -/
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
universe u

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine S] [Flat f]
variable (L : Line.Bundles.LineBundle X)
variable {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)

theorem orderedLineBundleCechObject_flat (q : ℕ)
    (hU : ∀ i : Fin (q + 1) → ι, IsAffineOpen (∏ᶜ fun k : Fin (q + 1) => U (i k))) :
    Module.Flat Γ(S, ⊤) (CoefficientCechTerms.orderedCoefficientCechObject f.appTop.hom L.sheaf U q) := by
  classical
  have : Finite (SectionCechIndices.OrderedCechIndex ι q) := inferInstanceAs
    (Finite {i : Fin (q + 1) → ι // StrictMono i})
  let : Fintype (SectionCechIndices.OrderedCechIndex ι q) := Fintype.ofFinite _
  have : ∀ i : SectionCechIndices.OrderedCechIndex ι q, Module.Flat Γ(S, ⊤) (CoefficientCechTerms.coefficientCechFactor f.appTop.hom L.sheaf U q i.1) :=
    fun i => HilbertConstruction.Flat.BaseLineBundleSections.flat_base_lineBundle_sections f L ⟨_, hU i.1⟩
  have : Module.Flat Γ(S, ⊤) (CoefficientCechTerms.orderedCoefficientCechTerm f.appTop.hom L.sheaf U q) :=
    Module.Flat.of_linearEquiv
      (DFinsupp.linearEquivFunOnFintype (R := Γ(S, ⊤))
        (M := fun i : SectionCechIndices.OrderedCechIndex ι q => ↥(CoefficientCechTerms.coefficientCechFactor f.appTop.hom L.sheaf U q i.1))).symm
  exact Module.Flat.of_linearEquiv (CoefficientCechTerms.orderedCoefficientCechObjectIsoPi f.appTop.hom L.sheaf U q).toLinearEquiv

theorem orderedLineBundleCechComplex_flat (hU : ∀ q (i : Fin (q + 1) → ι),
    IsAffineOpen (∏ᶜ fun k : Fin (q + 1) => U (i k))) (q : ℕ) :
    Module.Flat Γ(S, ⊤) ((CoefficientCechComplex.orderedCoefficientCechComplex f.appTop.hom L.sheaf U).X q) :=
  orderedLineBundleCechObject_flat f L U q (hU q)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.LineBundleCechFlat
