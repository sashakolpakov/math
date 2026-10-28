import OAI.RepresentationTheory.Theta.Geometric.FramedUnitIsomorphisms
import OAI.RepresentationTheory.Theta.Geometric.PowerGaugeCover

/-! # Framed Unit Restriction -/

namespace OAI.RepresentationTheory.Theta.Geometric.FramedUnitRestriction

noncomputable section

/-! Restriction of the native local isomorphisms defined by regular units. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def overIsoRestrict {X : Scheme.{u}} {M N : X.Modules} {U V : X.Opens} (h : V ≤ U)
    (e : M.over U ≅ N.over U) : M.over V ≅ N.over V :=
  (_root_.SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).symm.app M ≪≫
    (_root_.SheafOfModules.overMap X.ringCatSheaf (homOfLE h)).mapIso e ≪≫
    (_root_.SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).app N

theorem overIsoRestrict_trans {X : Scheme.{u}} {M N P : X.Modules} {U V : X.Opens}
    (h : V ≤ U) (e : M.over U ≅ N.over U) (g : N.over U ≅ P.over U) :
    overIsoRestrict h (e ≪≫ g) = overIsoRestrict h e ≪≫ overIsoRestrict h g := by
  apply Iso.ext
  exact AlgebraicGeometry.SheafCohomology.Projective.OverGeneratorRestriction.linearHomRestrict_comp M N P h e.hom g.hom

theorem overIsoRestrict_symm {X : Scheme.{u}} {M N : X.Modules} {U V : X.Opens}
    (h : V ≤ U) (e : M.over U ≅ N.over U) :
    overIsoRestrict h e.symm = (overIsoRestrict h e).symm := by
  apply Iso.ext
  simp only [overIsoRestrict, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Category.assoc]
  rfl

theorem overIsoRestrict_frame {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens}
    (h : V ≤ U) (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    overIsoRestrict (M := M) (N := AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) h e =
      AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U e (Over.mk (homOfLE h)) := by
  apply Iso.ext
  exact AlgebraicGeometry.SheafCohomology.Projective.FramedLocalHom.linearHomRestrict_frame M h e

theorem overScalar_restrict {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) (r : Γ(X, U)) :
    AlgebraicGeometry.SheafCohomology.Projective.LinearHom.linearHomRestrict X.ringCatSheaf (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)
      (homOfLE h).op (AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r) =
    AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf V (X.presheaf.map (homOfLE h).op r) := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (show Γ(X, Z.unop.left) from a) * X.presheaf.map (Z.unop.hom ≫ homOfLE h).op r =
    (show Γ(X, Z.unop.left) from a) *
      X.presheaf.map Z.unop.hom.op (X.presheaf.map (homOfLE h).op r)
  rw [op_comp, X.presheaf.map_comp_apply]

theorem overUnitIso_restrict {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) (r : Γ(X, U)ˣ) :
    overIsoRestrict (M := AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) (N := AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) h (FramedUnitIsomorphisms.overUnitIso U r) =
      FramedUnitIsomorphisms.overUnitIso V (PowerGaugeCover.restrictRegularUnit h r) := by
  apply Iso.ext
  exact overScalar_restrict h r

theorem framedUnitIso_restrict {X : Scheme.{u}} (M N : X.Modules) {U V : X.Opens} (h : V ≤ U)
    (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (g : N.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) (r : Γ(X, U)ˣ) :
    overIsoRestrict h (FramedUnitIsomorphisms.framedUnitIso M N U e g r) =
      FramedUnitIsomorphisms.framedUnitIso M N V
        (AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U e (Over.mk (homOfLE h)))
        (AlgebraicGeometry.SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf N U g (Over.mk (homOfLE h)))
        (PowerGaugeCover.restrictRegularUnit h r) := by
  have hg := (overIsoRestrict_symm (M := N) (N := AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) h g).trans
    (congrArg Iso.symm (overIsoRestrict_frame h g))
  have hr := (overIsoRestrict_trans (M := AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)
      (N := AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) (P := N) h (FramedUnitIsomorphisms.overUnitIso U r) g.symm).trans
    (congrArg₂ (fun a b => a ≪≫ b) (overUnitIso_restrict h r) hg)
  exact (overIsoRestrict_trans (M := M) (N := AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) (P := N)
      h e (FramedUnitIsomorphisms.overUnitIso U r ≪≫ g.symm)).trans
    (congrArg₂ (fun a b => a ≪≫ b) (overIsoRestrict_frame h e) hr)

end

end OAI.RepresentationTheory.Theta.Geometric.FramedUnitRestriction
