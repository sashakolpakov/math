import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SectionCounit
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoproductSectionIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Coproducts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Quasicoherence

/-! # Module Basis Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModuleBasisIsomorphism

noncomputable section

/-! An actual finite basis gives an isomorphism from a finite free structure sheaf to an affine quasicoherent module. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules
universe u

def affineModuleIsoOfBasis
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (I : Type u) [Fintype I] (b : Module.Basis I Γ(X, ⊤) Γ(M, ⊤)) :
    (∐ fun _ : I => Line.Bundles.structureModule X) ≅ M := by
  let C : X.Modules := ∐ fun _ : I => Line.Bundles.structureModule X
  have : C.IsQuasicoherent := Quasicoherent.Coproducts.module_quasicoherent_coproduct _
    (fun _ => (Line.Bundles.LineBundle.trivial X).isQuasicoherent)
  let e : (SectionAdjunction.AffineSectionAdjunction.sections X).obj C ≅
      (SectionAdjunction.AffineSectionAdjunction.sections X).obj M :=
    Finite.CoproductSectionIsomorphism.finiteCoproductSectionsIso (fun _ : I => Line.Bundles.structureModule X) ⊤ ≪≫ b.equivFun.symm.toModuleIso
  exact (SectionCounit.AffineSectionAdjunction.counitIso X C).symm ≪≫
    (SectionAdjunction.AffineSectionAdjunction.left X).mapIso e ≪≫ SectionCounit.AffineSectionAdjunction.counitIso X M

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModuleBasisIsomorphism
