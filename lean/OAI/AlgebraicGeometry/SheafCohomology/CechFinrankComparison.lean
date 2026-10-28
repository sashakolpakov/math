import OAI.AlgebraicGeometry.SheafCohomology.CoherentFiniteness
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechAllDegrees
import Mathlib.Algebra.Field.Equiv

/-! # Cech Finrank Comparison -/

namespace OAI.AlgebraicGeometry.SheafCohomology.CechFinrankComparison.Projective

noncomputable section

/-! Exact dimension comparison with the bounded Čech complex over the complex base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

@[instance_reducible]
def complexBaseSectionsField : Field Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField ℂ)).toField

theorem zariskiBase_finrank_eq_complex (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (M : A.carrier.Modules) (q : ℕ) :
    letI := Projective.BaseCechBridge.baseCohomologyModule A.variety.structureMap M q
    letI := Scalars.Projective.zariskiComplexCohomologyModule A M q
    Module.finrank Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) (AffineH.Projective.H M q) =
      Module.finrank ℂ (AffineH.Projective.H M q) := by
  let := Projective.BaseCechBridge.baseCohomologyModule A.variety.structureMap M q
  let := Scalars.Projective.zariskiComplexCohomologyModule A M q
  let e := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
  have h := _root_.rank_eq_of_equiv_equiv e (AddEquiv.refl (AffineH.Projective.H M q))
    e.bijective (fun r x => (CoherentFiniteness.Projective.zariskiBaseToComplexSemilinear A M q).map_smul' r x)
  exact congrArg Cardinal.toNat h

theorem coherent_finrank_eq_base (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (M : A.carrier.Modules) (q : ℕ) :
    letI := Projective.BaseCechBridge.baseCohomologyModule A.variety.structureMap M q
    Module.finrank ℂ (Sheaves.Projective.coherentCohomology A M q) =
      Module.finrank Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) (AffineH.Projective.H M q) := by
  let := Projective.BaseCechBridge.baseCohomologyModule A.variety.structureMap M q
  let := Scalars.Projective.zariskiComplexCohomologyModule A M q
  exact (LinearComparison.Projective.coherentCohomologyLinearEquivZariski A M q).finrank_eq.trans
    (zariskiBase_finrank_eq_complex A M q).symm

theorem coherent_finrank_eq_orderedBaseCech (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (M : A.carrier.Modules) [M.IsQuasicoherent]
    {ι : Type} [LinearOrder ι] (U : ι → A.carrier.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i)) (q : ℕ) :
    Module.finrank ℂ (Sheaves.Projective.coherentCohomology A M q) =
      Module.finrank Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤)
        ((Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex A.variety.structureMap M U).homology q) := by
  let : A.carrier.IsSeparated := by
    constructor
    rw [← CategoryTheory.Limits.terminal.comp_from A.variety.structureMap]
    infer_instance
  let := Projective.BaseCechBridge.baseCohomologyModule A.variety.structureMap M q
  exact (coherent_finrank_eq_base A M q).trans
    (Projective.BaseCechAllDegrees.orderedBaseCechHomologyAffineHLinearEquiv
      A.variety.structureMap M U hU hUaff q).finrank_eq.symm

end

end OAI.AlgebraicGeometry.SheafCohomology.CechFinrankComparison.Projective
