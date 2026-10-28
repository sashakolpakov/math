import OAI.AlgebraicGeometry.FormalGeometry.Completion.Polarization.TrivialitySieve
import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Functor

/-! # Group Condition -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.GroupCondition

noncomputable section

/-! The actual zero fiber of the polarization map is a subgroup on
every test scheme. The group operations descend from actual line classes
using the fppf sheaf condition. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) {T : Over (Spec (CommRingCat.of K))}

theorem polarizationFamilyClass_inv (a : T ⟶ A) :
    Polarization.Family.Construction.polarizationFamilyClass A L a⁻¹ = -Polarization.Family.Construction.polarizationFamilyClass A L a :=
  map_neg (Polarization.Family.Construction.polarizationFamilyHom A L T) (Additive.ofMul a)

theorem polarizationRelative_zero_mul (a b : T ⟶ A)
    (ha : Polarization.PicardMap.Construction.polarizationRelativeSection A L a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T)
    (hb : Polarization.PicardMap.Construction.polarizationRelativeSection A L b = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T) :
    Polarization.PicardMap.Construction.polarizationRelativeSection A L (a * b) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of K))
  apply (Polarization.TrivialitySieve.Construction.polarizationTrivialitySieve_mem_iff A L (a * b)).mp
  apply J.superset_covering _ (J.intersection_covering
    ((Polarization.TrivialitySieve.Construction.polarizationTrivialitySieve_mem_iff A L a).mpr ha)
    ((Polarization.TrivialitySieve.Construction.polarizationTrivialitySieve_mem_iff A L b).mpr hb))
  intro U j hj
  apply (Polarization.TrivialitySieve.Construction.polarizationTrivialitySieve_apply A L (a * b) j).mpr
  rw [MonObj.comp_mul, Polarization.Family.Construction.polarizationFamilyClass_mul,
    (Polarization.TrivialitySieve.Construction.polarizationTrivialitySieve_apply A L a j).mp hj.1,
    (Polarization.TrivialitySieve.Construction.polarizationTrivialitySieve_apply A L b j).mp hj.2, add_zero]

theorem polarizationRelative_zero_inv (a : T ⟶ A)
    (ha : Polarization.PicardMap.Construction.polarizationRelativeSection A L a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T) :
    Polarization.PicardMap.Construction.polarizationRelativeSection A L a⁻¹ = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of K))
  apply (Polarization.TrivialitySieve.Construction.polarizationTrivialitySieve_mem_iff A L a⁻¹).mp
  apply J.superset_covering _ ((Polarization.TrivialitySieve.Construction.polarizationTrivialitySieve_mem_iff A L a).mpr ha)
  intro U j hj
  apply (Polarization.TrivialitySieve.Construction.polarizationTrivialitySieve_apply A L a⁻¹ j).mpr
  rw [GrpObj.comp_inv, polarizationFamilyClass_inv,
    (Polarization.TrivialitySieve.Construction.polarizationTrivialitySieve_apply A L a j).mp hj, neg_zero]

def polarizationKernelPoints (T : Over (Spec (CommRingCat.of K))) : Subgroup (T ⟶ A) where
  carrier := { a | Polarization.PicardMap.Construction.polarizationRelativeSection A L a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T }
  one_mem' := Polarization.PicardMap.Construction.polarizationRelativeSection_one A L T
  mul_mem' := polarizationRelative_zero_mul A L _ _
  inv_mem' := polarizationRelative_zero_inv A L _

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.GroupCondition
