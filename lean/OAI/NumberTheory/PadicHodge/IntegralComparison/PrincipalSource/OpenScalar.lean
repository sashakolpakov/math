import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SubschemeCoefficientUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenFixedClass

/-! # Open Scalar -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenScalar

noncomputable section

/-! The source-open scalar action is the original ambient principal
action, transported through the actual restriction unit. The additive
coordinates retain the original two pushforwards and restriction map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenRestriction
variable {Y X Z : Scheme.{u}} (f : Y ⟶ X) (i : X ⟶ Z)
  (U : Z.Opens) (hU : IsAffineOpen U) (N : Y.Modules)

abbrev ambient : Y.Opens := (f ≫ i) ⁻¹ᵁ U

def coefficientScalar (z : Γ(Y,ambient f i U)) :
    OpenRestriction.image f i (OpenRestriction.extension (ambient f i U) N) ⟶ OpenRestriction.image f i (OpenRestriction.extension (ambient f i U) N) :=
  (Scheme.Modules.pushforward i).map ((Scheme.Modules.pushforward f).map
    (Open.SubschemeCoefficientUnit.scalar (ambient f i U) N z))

def scalarMap (z : Γ(Y,ambient f i U)) := Principal.SectionPresheaf.moduleHom U hU (coefficientScalar f i U N z)

theorem scalar_unit (z : Γ(Y,ambient f i U)) :
    OpenFixedClass.scalar f i U hU N z ≫ OpenRestriction.map f i U hU (ambient f i U) N =
      OpenRestriction.map f i U hU (ambient f i U) N ≫ scalarMap f i U hU N z := by
  apply NatTrans.ext
  funext r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let O := Principal.ClosedScalars.pullbackOpen (f ≫ i) U r.unop
  let a := homOfLE ((ambient f i U).ι.image_preimage_le O)
  change N.presheaf.map a.op
      (Y.presheaf.map
        (Principal.ClosedScalars.pullbackInclusion (f ≫ i) U r.unop).op z •
        (show Γ(N,O) from x)) =
    (Open.SubschemeCoefficientUnit.scalar (ambient f i U) N z).app O (N.presheaf.map a.op x)
  rw [Open.SubschemeCoefficientUnit.scalar_app, N.map_smul]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← Y.presheaf.map_comp]
  rfl

private abbrev sections (M : Y.Modules) : Y.Opensᵒᵖ ⥤ AddCommGrpCat.{u} :=
  ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M).obj

def diagramIso :
    OpenFixedClass.source f i U hU N ⋙ Principal.AdditiveSections.forgetScalars U ≅
      (OpenReindex.wideOpens (f ≫ i) U hU).op ⋙ sections N :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {_ _} _ => rfl)

variable {N} {P : Y.Modules} (a : N ⟶ P)

theorem diagramIso_natural :
    Functor.whiskerRight
      (Principal.SectionPresheaf.moduleHom U hU ((Scheme.Modules.pushforward i).map ((Scheme.Modules.pushforward f).map a)))
      (Principal.AdditiveSections.forgetScalars U) ≫ (diagramIso f i U hU P).hom =
    (diagramIso f i U hU N).hom ≫
      Open.SubschemeSectionDiagram.coefficientMap
        (OpenReindex.wideOpens (f ≫ i) U hU) a := by
  apply NatTrans.ext
  funext r
  rfl

variable (N) (V : Y.Opens)

def localDiagramIso :
    OpenFixedClass.source f i U hU (OpenRestriction.extension V N) ⋙
        Principal.AdditiveSections.forgetScalars U ≅
      OpenReindex.geometricSections (f ≫ i) U hU V N :=
  diagramIso f i U hU (OpenRestriction.extension V N) ≪≫
    (OpenReindex.pushforwardIso (f ≫ i) U hU (OpenRestriction.extension V N)).symm ≪≫
      OpenReindex.extensionIso (f ≫ i) U hU V N

theorem localDiagramIso_apply (r : Principal.SectionPresheaf.Index U)
    (x : Γ(N,V.ι ''ᵁ (V.ι ⁻¹ᵁ ((f ≫ i) ⁻¹ᵁ Principal.SectionPresheaf.openSubset U r)))) :
    (localDiagramIso f i U hU N V).hom.app (op r) x =
      N.presheaf.map
        (eqToHom (OpenReindex.extensionOpen_eq (f ≫ i) U hU V r).symm).op x := rfl

def additiveRestriction :
    OpenFixedClass.source f i U hU N ⋙ Principal.AdditiveSections.forgetScalars U ⟶
      OpenFixedClass.source f i U hU (OpenRestriction.extension V N) ⋙
        Principal.AdditiveSections.forgetScalars U :=
  Functor.whiskerRight (OpenRestriction.map f i U hU V N) (Principal.AdditiveSections.forgetScalars U)

def geometricRestriction :
    (OpenReindex.wideOpens (f ≫ i) U hU).op ⋙ sections N ⟶
      OpenReindex.geometricSections (f ≫ i) U hU V N :=
  Functor.whiskerRight
    (NatTrans.op (OpenReindex.geometricInclusion (f ≫ i) U hU V)) (sections N)

theorem restriction_apply (r : Principal.SectionPresheaf.Index U) (x : Γ(N,(f ≫ i) ⁻¹ᵁ Principal.SectionPresheaf.openSubset U r)) :
    (localDiagramIso f i U hU N V).hom.app (op r) ((OpenRestriction.map f i U hU V N).app (op r) x) =
      N.presheaf.map ((OpenReindex.geometricInclusion (f ≫ i) U hU V).app r).op x := by
  rw [localDiagramIso_apply f i U hU N V r ((OpenRestriction.map f i U hU V N).app (op r) x)]
  rw [OpenRestriction.map_app f i U hU V N r x]
  erw [← ConcreteCategory.comp_apply, ← N.presheaf.map_comp]
  rfl

theorem restriction_square :
    additiveRestriction f i U hU N V ≫ (localDiagramIso f i U hU N V).hom =
      (diagramIso f i U hU N).hom ≫ geometricRestriction f i U hU N V := by
  apply NatTrans.ext
  funext r
  apply ConcreteCategory.hom_ext
  intro x
  exact restriction_apply f i U hU N V r.unop x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenScalar
