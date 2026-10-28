import OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.OrderedCechQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.InjectiveIntegerCoordinates
import OAI.AlgebraicGeometry.SheafCohomology.Cech.Cochains
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.SupportedExtension

/-! # Ordered Injective -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.OrderedInjective.Comparison

noncomputable section

/-! The actual augmentation from a single quasicoherent sheaf to its
chosen shifted injective resolution is an isomorphism on affine ordered
Cech cohomology. Its inverse returns to the original global Cech group. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Injective.Comparison
variable {X : Scheme.{u}} (N : X.Modules) (c : ℕ)

def sourcePresheaf : CochainComplex (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ :=
  ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex
    (.up ℕ)).obj ((single _ (.up ℕ) c).obj (AffinePrincipal.Injective.Comparison.sheaf N))

def targetPresheaf : CochainComplex (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ :=
  ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex
    (.up ℕ)).obj (ShiftedOpenInjectiveResolution.complex (AffinePrincipal.Injective.Comparison.sheaf N) c)

def augmentation : sourcePresheaf N c ⟶ targetPresheaf N c :=
  ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex
    (.up ℕ)).map (ShiftedOpenInjectiveResolution.augmentation (AffinePrincipal.Injective.Comparison.sheaf N) c)

variable {ι : Type u} [LinearOrder ι] (V : ι → X.Opens)

abbrev source := (Presheaf.OrderedCover.Comparison.totalFunctor V).obj (sourcePresheaf N c)
abbrev target := (Presheaf.OrderedCover.Comparison.totalFunctor V).obj (targetPresheaf N c)
def comparison : source N c V ⟶ target N c V :=
  (Presheaf.OrderedCover.Comparison.totalFunctor V).map (augmentation N c)

theorem quasiIso [X.IsSeparated] [N.IsQuasicoherent] (hV : ∀ j, IsAffineOpen (V j)) :
    QuasiIso (comparison N c V) := by
  apply Additive.OrderedCechQuasiIso.quasiIso_of_evaluation
  intro p j
  change QuasiIso
    (((Acyclic.OpenInjectiveResolution.sections
      ((AugmentedOrdered.Cech.formal V (p+1)).obj j)).mapHomologicalComplex (.up ℕ)).map
        (ShiftedOpenInjectiveResolution.augmentation (AffinePrincipal.Injective.Comparison.sheaf N) c))
  exact ShiftedOpenInjectiveResolution.sections_quasiIso (AffinePrincipal.Injective.Comparison.sheaf N) c _
    (fun q => AffinePrincipal.Injective.Comparison.affine_acyclic N _ (AlgebraicGeometry.SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection V hV p j.val) q)

def homologyIso [X.IsSeparated] [N.IsQuasicoherent] (hV : ∀ j, IsAffineOpen (V j)) (q : ℕ) :
    (source N c V).homology q ≅ (target N c V).homology q :=
  letI := quasiIso N c V hV
  isoOfQuasiIsoAt (comparison N c V) q

def integerPresheaf : CochainComplex (X.Opensᵒᵖ ⥤ ModuleCat.{u} ℤ) ℕ :=
  Relative.SupportedExtension.underlying.{0,u,u} ℤ X (Principal.InjectiveIntegerCoordinates.complex N c)

def coefficientIso (q : ℕ) :
    Principal.InjectiveIntegerCoordinates.forget.obj
      (((Presheaf.OrderedCover.Comparison.totalFunctor V).obj (integerPresheaf N c)).homology q) ≅
    (target N c V).homology q :=
  OrderedCech.CoefficientTotal.homologyIso V Principal.InjectiveIntegerCoordinates.forget
    (integerPresheaf N c) q

def bridge [X.IsSeparated] [N.IsQuasicoherent] (hV : ∀ j, IsAffineOpen (V j)) (q : ℕ) :=
  coefficientIso N c V q ≪≫ (homologyIso N c V hV q).symm

def coverOutput [X.IsSeparated] [N.IsQuasicoherent] (hV : ∀ j, IsAffineOpen (V j)) (q : ℕ) :
    (Principal.InjectiveIntegerCoordinates.additiveGlobalComplex N c).homology q ⟶
      (source N c V).homology q :=
  (Principal.InjectiveIntegerCoordinates.globalIso N c q).inv ≫
    Principal.InjectiveIntegerCoordinates.forget.map
      (homologyMap (Presheaf.OrderedCechEdge.edge V (integerPresheaf N c)) q) ≫
    (bridge N c V hV q).hom

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.OrderedInjective.Comparison
