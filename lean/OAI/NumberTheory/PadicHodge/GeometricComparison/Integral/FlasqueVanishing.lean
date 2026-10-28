import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.AdditiveSheafCohomology
import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.InjectiveFlasque
import OAI.AlgebraicGeometry.SheafCohomology.FlasqueVanishing

/-! # Flasque Vanishing -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FlasqueVanishing.IntegralFlasqueVanishing

noncomputable section

/-! Flasque native coefficient sheaves over flat integer algebras have vanishing positive Ext. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] [Module.Flat ℤ R]
  (X : Over (Spec (CommRingCat.of R))) (F : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) [TopCat.Sheaf.IsFlasque F]

local notation "J" => Opens.grothendieckTopology X.left

local instance : HasExt.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) := HasExt.standard _
local instance : HasExt.{0} (Sheaf J (ModuleCat ℤ)) := hasExt_of_enoughInjectives _
local instance : HasExt.{0} (Sheaf J AddCommGrpCat) := hasExt_of_enoughInjectives _

omit [Module.Flat ℤ R] in
theorem underlying_flasque :
    AlgebraicGeometry.SheafCohomology.FlasqueVanishing.Projective.IsFlasqueSheaf (AdditiveSheafCohomology.IntegralAdditiveSheafCohomology.underlyingSheaf R J F) := by
  intro U V i
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  exact (ModuleCat.epi_iff_surjective (F.obj.map i.op)).mp
    (TopCat.Presheaf.IsFlasque.epi (F := F.obj) i.op)

theorem ext_subsingleton (n : ℕ) :
    Subsingleton (Abelian.Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X) F (n + 1)) := by
  let : Subsingleton (Sheaf.H (AdditiveSheafCohomology.IntegralAdditiveSheafCohomology.underlyingSheaf R J F) (n + 1)) :=
    AlgebraicGeometry.SheafCohomology.FlasqueVanishing.Projective.sheafH_subsingleton_of_flasque (TopCat.of X.left) _ (underlying_flasque R X F) n
  exact (AdditiveSheafCohomology.IntegralAdditiveSheafCohomology.equiv R J F (n + 1)).injective.subsingleton

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FlasqueVanishing.IntegralFlasqueVanishing
