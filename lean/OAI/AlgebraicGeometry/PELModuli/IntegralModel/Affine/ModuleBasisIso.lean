import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineSectionIs
import OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation

/-! # Module Basis Iso -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.ModuleBasisIso

noncomputable section

/-! An actual finite basis of affine sections gives an isomorphism from
a finite coproduct of the structure module to the original sheaf. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

def affineModuleIsoOfBasis
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (I : Type) [Fintype I] (b : Module.Basis I Γ(X, ⊤) Γ(M, ⊤)) :
    (∐ fun _ : I => SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) ≅ M := by
  let C := ∐ fun _ : I => SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X
  have : C.IsQuasicoherent := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_coproduct _
    (fun _ => SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent SheafCohomology.Projective.Invertible.Scheme.Modules.isInvertible_unit)
  let F : X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤) :=
    SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)
  have : F.Additive := { map_add := by intros; ext x; rfl }
  letI : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts
  let eR : F.obj (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) ≅ ModuleCat.of Γ(X, ⊤) Γ(X, ⊤) := Iso.refl _
  let e : F.obj C ≅ F.obj M :=
    SheafCohomology.Projective.AdditiveCoproductSections.additiveCoproductIsoPi F (fun _ : I => SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) ≪≫
      (LinearEquiv.piCongrRight (fun _ : I => eR.toLinearEquiv)).toModuleIso ≪≫
        b.equivFun.symm.toModuleIso
  exact (Quotients.FiniteDescent.AffineSectionIs.Construction.AffineSectionAdjunction.counitIso X C).symm ≪≫
    (Quotients.FiniteDescent.AffineSectionIs.Construction.AffineSectionAdjunction.left X).mapIso e ≪≫
      Quotients.FiniteDescent.AffineSectionIs.Construction.AffineSectionAdjunction.counitIso X M

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.ModuleBasisIso
