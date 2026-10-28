import OAI.AlgebraicGeometry.ComplexMultiplication.OpenSupportedCohomologyNormalization
import OAI.AlgebraicTopology.Support.SingularCohomologySheafComparison

/-! # Supported Singular Sheaf Normalization -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.SupportedSingularSheafNormalization

noncomputable section

/-! # The original supported cohomology sheaf has the actual relative-class normalization -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open OAI.AlgebraicTopology.Singular _root_.TopCat.Sheaf

variable (Y : TopCat.{0}) [T2Space Y] [∀ W : Opens Y, ParacompactSpace W]
  (S : Set Y) (hS : IsClosed S) (n : ℕ) (V : Opens Y)

local notation "K" => OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex Y (Opens.mk Sᶜ hS.isOpen_compl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Taking a section-complex class to its cohomology sheaf agrees with literal relative sheafification. -/
theorem supportedSingularSheaf_normalization :
    AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyToSheafSection Y (K) (n : ℤ) V ≫
      (AlgebraicTopology.Support.SingularCohomologySheafComparison.Singular.supportedSingularCohomologySheafIsoRelative Y S hS n).hom.hom.app (op V) =
    (AlgebraicTopology.Support.SingularSectionCohomology.Singular.supportedRationalSingularSectionCohomologyEquivSupportComplement Y S hS V n).toAddCommGrpIso.hom ≫
      (AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyToSheaf Y S n).app (op V) := by
  let e := (sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat).mapIso
    (AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyPresheafSheafificationIso Y (K) (n : ℤ))
  let j := AlgebraicTopology.Support.SingularCohomologySheafComparison.Singular.supportedSingularCohomologyPresheafIsoRelative Y S hS n
  change (AlgebraicTopology.Sheaf.CohomologyStalkVanishing.TopCat.sectionCohomologyPresheafOnOpenIso Y (K) (n : ℤ) V).hom ≫
    ((toSheafify (Opens.grothendieckTopology Y) _ ≫ e.hom) ≫
      (e.inv ≫ sheafifyMap (Opens.grothendieckTopology Y) j.hom)).app (op V) = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← toSheafify_naturality, NatTrans.comp_app]
  change (AlgebraicTopology.Sheaf.CohomologyStalkVanishing.TopCat.sectionCohomologyPresheafOnOpenIso Y (K) (n : ℤ) V).hom ≫
    ((AlgebraicTopology.Sheaf.CohomologyStalkVanishing.TopCat.sectionCohomologyPresheafOnOpenIso Y (K) (n : ℤ) V).inv ≫
      (AlgebraicTopology.Support.SingularSectionCohomology.Singular.supportedRationalSingularSectionCohomologyEquivSupportComplement Y S hS V n).toAddCommGrpIso.hom) ≫
        (AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyToSheaf Y S n).app (op V) = _
  simp

end

end OAI.AlgebraicGeometry.ComplexMultiplication.SupportedSingularSheafNormalization
