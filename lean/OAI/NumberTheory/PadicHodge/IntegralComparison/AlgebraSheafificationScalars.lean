import OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafScalars
import OAI.NumberTheory.PadicHodge.IntegralComparison.SchemeModuleSheafification

/-! # Algebra Sheafification Scalars -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafificationScalars

noncomputable section

/-!
# IntegralComparison: base-ring scalar restriction commutes with native module sheafification
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) [CommRing k] (X : Over (Spec (CommRingCat.of k)))

local notation "J" => Opens.grothendieckTopology X.left
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafScalars.presheaves k X
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafScalars.functor k X
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.SchemeModuleSheafification.functor X.left

def unit (M : PresheafOfModules.{u} X.left.ringCatSheaf.obj) :
    (P).obj M ⟶ ((S).obj ((L).obj M)).obj :=
  (P).map ((PresheafOfModules.sheafificationAdjunction (𝟙 X.left.ringCatSheaf.obj)).unit.app M)

instance unit_locallyInjective (M : PresheafOfModules.{u} X.left.ringCatSheaf.obj) :
    Presheaf.IsLocallyInjective J (AlgebraSheafificationScalars.unit k X M) := by
  apply (Presheaf.isLocallyInjective_forget_iff J (AlgebraSheafificationScalars.unit k X M)).mp
  exact inferInstanceAs (Presheaf.IsLocallyInjective J
    (Functor.whiskerRight (toSheafify J M.presheaf) (forget AddCommGrpCat.{u})))

instance unit_locallySurjective (M : PresheafOfModules.{u} X.left.ringCatSheaf.obj) :
    Presheaf.IsLocallySurjective J (AlgebraSheafificationScalars.unit k X M) := by
  apply (Presheaf.isLocallySurjective_iff_whisker_forget J (AlgebraSheafificationScalars.unit k X M)).mpr
  exact inferInstanceAs (Presheaf.IsLocallySurjective J
    (Functor.whiskerRight (toSheafify J M.presheaf) (forget AddCommGrpCat.{u})))

def map (M : PresheafOfModules.{u} X.left.ringCatSheaf.obj) :
    (presheafToSheaf J (ModuleCat.{u} k)).obj ((P).obj M) ⟶ (S).obj ((L).obj M) :=
  ((sheafificationAdjunction J (ModuleCat.{u} k)).homEquiv _ _).symm (AlgebraSheafificationScalars.unit k X M)

theorem map_fac (M : PresheafOfModules.{u} X.left.ringCatSheaf.obj) :
    toSheafify J ((P).obj M) ≫ (AlgebraSheafificationScalars.map k X M).hom = AlgebraSheafificationScalars.unit k X M :=
  ((sheafificationAdjunction J (ModuleCat.{u} k)).homEquiv _ _).apply_symm_apply _

instance map_isIso (M : PresheafOfModules.{u} X.left.ringCatSheaf.obj) : IsIso (AlgebraSheafificationScalars.map k X M) := by
  have h : (J).W ((AlgebraSheafificationScalars.map k X M).hom) := (J).W.of_precomp (W' := (J).W)
    (toSheafify J ((P).obj M)) ((AlgebraSheafificationScalars.map k X M).hom) ((J).W_toSheafify _)
      ((map_fac k X M).symm ▸ (J).W_of_isLocallyBijective (AlgebraSheafificationScalars.unit k X M))
  exact (Sheaf.isLocallyBijective_iff_isIso (AlgebraSheafificationScalars.map k X M)).mp
    ⟨h.isLocallyInjective, h.isLocallySurjective⟩

theorem unit_naturality {M N : PresheafOfModules.{u} X.left.ringCatSheaf.obj} (f : M ⟶ N) :
    (P).map f ≫ AlgebraSheafificationScalars.unit k X N = AlgebraSheafificationScalars.unit k X M ≫ ((S).map ((L).map f)).hom :=
  ((P).map_comp _ _).symm.trans
    ((congrArg (P).map ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.left.ringCatSheaf.obj)).unit.naturality f)).trans ((P).map_comp _ _))

theorem naturality {M N : PresheafOfModules.{u} X.left.ringCatSheaf.obj} (f : M ⟶ N) :
    (presheafToSheaf J (ModuleCat.{u} k)).map ((P).map f) ≫ AlgebraSheafificationScalars.map k X N =
      AlgebraSheafificationScalars.map k X M ≫ (S).map ((L).map f) :=
  (sheafificationAdjunction J (ModuleCat.{u} k)).homEquiv_naturality_right_square
    (Y := (S).obj ((L).obj M)) (Y' := (S).obj ((L).obj N))
    ((P).map f) (AlgebraSheafificationScalars.unit k X N) (AlgebraSheafificationScalars.unit k X M) ((S).map ((L).map f)) (unit_naturality k X f)

def objectIso (M : PresheafOfModules.{u} X.left.ringCatSheaf.obj) :
    (presheafToSheaf J (ModuleCat.{u} k)).obj ((P).obj M) ≅ (S).obj ((L).obj M) := by
  let : IsIso (AlgebraSheafificationScalars.map k X M) := map_isIso k X M
  exact asIso (AlgebraSheafificationScalars.map k X M)

def iso : (P) ⋙ presheafToSheaf J (ModuleCat.{u} k) ≅ (L) ⋙ (S) :=
  NatIso.ofComponents (objectIso k X) (fun f => AlgebraSheafificationScalars.naturality k X f)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafificationScalars
