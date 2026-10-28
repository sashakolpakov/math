import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.ZeroCohomologyTensor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.CohomologyRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.EquivalentDimensions
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Section Dimensions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.SectionDimensions

noncomputable section

/-! The linear tensor comparison gives the product formula for the actual
ground-field dimensions of the global sections of an external line bundle. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem coefficientCohomology_finrank_specGlobalRing
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (M : X.Modules) (q : ℕ) :
    Module.finrank k ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap f) q).obj M) =
      Module.finrank Γ(Spec (.of k), ⊤)
        ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom q).obj M) := by
  let e : k ≃+* Γ(Spec (.of k), ⊤) :=
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm
  let V := (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom q).obj M
  let h := CoefficientCohomology.CohomologyRestriction.coefficientCohomologyRestrictionIso e.toRingHom f.appTop.hom M q
  have hh : Module.finrank k
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap f) q).obj M) =
      Module.finrank k ((ModuleCat.restrictScalars e.toRingHom).obj V) := h.toLinearEquiv.finrank_eq.symm
  exact hh.trans (Scalar.EquivalentDimensions.restrictScalars_finrank_of_ringEquiv e V)

variable {k : Type u} [Field k] {X Y P : Scheme.{u}}
variable [X.IsSeparated] [Y.IsSeparated] [P.IsSeparated]
variable {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Spec (.of k)} {g : Y ⟶ Spec (.of k)}
variable (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X) (N : Line.Bundles.LineBundle Y)
variable {ι : Type u} [Finite ι] (V : ι → X.Opens)
variable (hV : iSup V = ⊤) (haV : ∀ i, IsAffineOpen (V i))
variable (heV : ∀ i, Nonempty ((Scheme.Modules.pullback (V i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (V i).toScheme))
variable {κ : Type u} [Finite κ] (U : κ → Y.Opens) (haU : ∀ i, IsAffineOpen (U i))
variable (heU : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj N.sheaf ≅ Line.Bundles.structureModule (U i).toScheme))

include H V hV haV heV haU heU in
theorem fieldExternalZeroCohomology_finrank (hU : iSup U = ⊤) :
    Module.finrank k ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap (b ≫ g)) 0).obj (((L.pullback a).tensor (N.pullback b)).sheaf)) =
    Module.finrank k ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap f) 0).obj L.sheaf) *
    Module.finrank k ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap g) 0).obj N.sheaf) := by
  let : Field Γ(Spec (.of k), ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)).toField
  rw [coefficientCohomology_finrank_specGlobalRing, coefficientCohomology_finrank_specGlobalRing,
    coefficientCohomology_finrank_specGlobalRing]
  have hcomp : (b ≫ g).appTop.hom = b.appTop.hom.comp g.appTop.hom := by
    rw [Scheme.Hom.comp_appTop]
    rfl
  rw [hcomp]
  have h := (ZeroCohomologyTensor.fieldExternalZeroCohomologyModuleIso H L N V hV haV heV U haU heU hU).toLinearEquiv.finrank_eq
  rw [← h]
  have ht := (Module.finrank_tensorProduct
    (R := Γ(Spec (.of k), ⊤)) (S := Γ(Spec (.of k), ⊤))
    (M := (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor g.appTop.hom 0).obj N.sheaf)
    (M' := (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor f.appTop.hom 0).obj L.sheaf))
  rw [Nat.mul_comm] at ht
  exact ht

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.SectionDimensions
