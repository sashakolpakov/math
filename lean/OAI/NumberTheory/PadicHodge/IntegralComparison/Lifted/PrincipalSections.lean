import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalOpens
import OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.AffineAcyclicity

/-! # Principal Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.PrincipalSections

noncomputable section

/-!
# IntegralComparison: principal sections commute with the actual ambient-ring universe lift

Localization identifies the lifted original sections with sections on
the spectrum of the lifted ring, naturally in every principal open.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalOpens.Category

universe u

variable (R : Type u) [CommRing R]

abbrev LiftedRing := AffineAcyclicity.LiftedRing R

abbrev toLiftedOpens : PrincipalOpens.Category.Principal R ⥤ TopologicalSpace.Opens (PrimeSpectrum (LiftedRing R)) :=
  PrincipalOpens.Category.toOpens R ⋙ (ZariskiHomeomorphism.opensEquiv
    (AffineAcyclicity.spectrumHomeomorph R)).inverse

theorem toLiftedOpens_obj (r : PrincipalOpens.Category.Principal R) :
    (toLiftedOpens R).obj r = PrimeSpectrum.basicOpen (ULift.up r.function : LiftedRing R) := rfl

abbrev Sections (r : PrincipalOpens.Category.Principal R) :=
  (Spec.structureSheaf R).obj.obj (op (PrimeSpectrum.basicOpen r.function))

abbrev LiftedSections (r : PrincipalOpens.Category.Principal R) :=
  (Spec.structureSheaf (LiftedRing R)).obj.obj (op ((toLiftedOpens R).obj r))

instance sectionsAlgebra (r : PrincipalOpens.Category.Principal R) : Algebra R (Sections R r) :=
  StructureSheaf.openAlgebra R _

instance sectionsLocalization (r : PrincipalOpens.Category.Principal R) : IsLocalization.Away r.function (Sections R r) :=
  StructureSheaf.IsLocalization.to_basicOpen R r.function

instance liftedSectionsAlgebra (r : PrincipalOpens.Category.Principal R) : Algebra (LiftedRing R) (LiftedSections R r) :=
  StructureSheaf.openAlgebra (LiftedRing R) _

instance liftedSectionsLocalization (r : PrincipalOpens.Category.Principal R) :
    IsLocalization.Away (ULift.up r.function : LiftedRing R) (LiftedSections R r) :=
  StructureSheaf.IsLocalization.to_basicOpen (LiftedRing R) (ULift.up r.function)

def sectionsEquiv (r : PrincipalOpens.Category.Principal R) : Sections R r ≃+* LiftedSections R r :=
  IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers r.function)
    (T := Submonoid.powers (ULift.up r.function : LiftedRing R)) (Sections R r) (LiftedSections R r)
    (ULift.ringEquiv : LiftedRing R ≃+* R).symm (by rw [Submonoid.map_powers]; rfl)

theorem sectionsEquiv_algebraMap (r : PrincipalOpens.Category.Principal R) (x : R) :
    sectionsEquiv R r (algebraMap R (Sections R r) x) =
      algebraMap (LiftedRing R) (LiftedSections R r) (ULift.up x) := by
  unfold sectionsEquiv
  exact IsLocalization.ringEquivOfRingEquiv_eq _ _

abbrev smallPresheaf := (PrincipalOpens.Category.toOpens R).op ⋙ (Spec.structureSheaf R).obj
abbrev liftedPresheaf := (toLiftedOpens R).op ⋙ (Spec.structureSheaf (LiftedRing R)).obj

theorem sections_natural {r s : PrincipalOpens.Category.Principal R} (a : r ⟶ s) :
    (sectionsEquiv R r).toRingHom.comp ((smallPresheaf R).map a.op).hom =
      ((liftedPresheaf R).map a.op).hom.comp (sectionsEquiv R s).toRingHom := by
  apply IsLocalization.ringHom_ext (S := Sections R s) (Submonoid.powers s.function)
  apply RingHom.ext
  intro x
  change sectionsEquiv R r ((smallPresheaf R).map a.op (algebraMap R (Sections R s) x)) =
    (liftedPresheaf R).map a.op (sectionsEquiv R s (algebraMap R (Sections R s) x))
  rw [sectionsEquiv_algebraMap]
  change sectionsEquiv R r (algebraMap R (Sections R r) x) =
    algebraMap (LiftedRing R) (LiftedSections R r) (ULift.up x)
  exact sectionsEquiv_algebraMap R r x

theorem sections_natural_apply {r s : PrincipalOpens.Category.Principal R} (a : r ⟶ s) (x : Sections R s) :
    sectionsEquiv R r ((smallPresheaf R).map a.op x) =
      (liftedPresheaf R).map a.op (sectionsEquiv R s x) :=
  DFunLike.congr_fun (sections_natural R a) x

abbrev forgetAdd : CommRingCat.{u} ⥤ AddCommGrpCat.{u} :=
  forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}

def additivePresheafIso :
    smallPresheaf R ⋙ forgetAdd ⋙ AddCommGrpCat.uliftFunctor.{u + 1} ≅
      liftedPresheaf R ⋙ forgetAdd :=
  NatIso.ofComponents
    (fun r => ((AddEquiv.ulift : ULift.{u + 1} (Sections R r.unop) ≃+ Sections R r.unop).trans
      (sectionsEquiv R r.unop).toAddEquiv).toAddCommGrpIso)
    (fun a => by
      apply AddCommGrpCat.hom_ext
      ext x
      exact sections_natural_apply R a.unop x.down)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.PrincipalSections
