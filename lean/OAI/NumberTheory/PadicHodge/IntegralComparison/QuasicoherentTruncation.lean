import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Cokernels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Coproducts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Kernels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.QuasicoherenceLocality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictionGeneratingSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TypeFromAffineSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentFiniteTypeSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FiniteGeneratingSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CoherentHomology
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Quasicoherent Truncation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.QuasicoherentTruncation

noncomputable section

/-! Canonical truncation preserves quasicoherence of the actual sheaf
complex, including its boundary quotient and its zero terms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}}

theorem of_isZero (M : X.Modules) (hM : IsZero M) : M.IsQuasicoherent := by
  let F : X.Modules := SheafOfModules.free PEmpty.{u + 1}
  have hf : IsZero F := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply Limits.Sigma.hom_ext
    intro i
    exact isEmptyElim i
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (hf.iso hM) inferInstance

variable (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]

theorem opcycles (q : ℕ) : (K.opcycles q).IsQuasicoherent := by
  have h : (cokernel (K.sc q).f).IsQuasicoherent :=
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Cokernels.module_quasicoherent_cokernel (K.d ((ComplexShape.up ℕ).prev q) q)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (K.sc q).opcyclesIsoCokernel.symm h

theorem cohomology (q : ℕ) : (K.homology q).IsQuasicoherent := by
  have : (K.sc q).X₁.IsQuasicoherent := inferInstanceAs (K.X ((ComplexShape.up ℕ).prev q)).IsQuasicoherent
  have : (K.sc q).X₂.IsQuasicoherent := inferInstanceAs (K.X q).IsQuasicoherent
  have : (K.sc q).X₃.IsQuasicoherent := inferInstanceAs (K.X ((ComplexShape.up ℕ).next q)).IsQuasicoherent
  exact Module.CoherentHomology.quasicoherent (K.sc q)

theorem truncation (c q : ℕ) : ((CohomologyConcentration.truncation K c).X q).IsQuasicoherent := by
  let e := CohomologyConcentration.shift c
  by_cases hq : ∃ i, e.f i = q
  · obtain ⟨i, rfl⟩ := hq
    by_cases hi : e.BoundaryGE i
    · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        (HomologicalComplex.truncGEXIsoOpcycles K e rfl hi).symm (QuasicoherentTruncation.opcycles K (e.f i))
    · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        (HomologicalComplex.truncGEXIso K e rfl hi).symm inferInstance
  · exact of_isZero _ (HomologicalComplex.isZero_extend_X _ e q (by simpa using hq))

theorem single (M : X.Modules) [M.IsQuasicoherent] (c q : ℕ) :
    (((HomologicalComplex.single X.Modules (.up ℕ) c).obj M).X q).IsQuasicoherent := by
  by_cases hq : q = c
  · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (HomologicalComplex.singleObjXIsoOfEq (.up ℕ) c M q hq).symm inferInstance
  · exact of_isZero _ (HomologicalComplex.isZero_single_obj_X (.up ℕ) c M q hq)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.QuasicoherentTruncation
