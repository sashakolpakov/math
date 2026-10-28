import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleScalars
import OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafificationScalars
import OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.LocalizingBasis
import Mathlib

/-! # Localizing Module -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LocalizingModule

noncomputable section

/-!
# IntegralComparison: affine module presheaves that localize yield the original quasicoherent module sheaf
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (A : Type u) [CommRing A]
  (M : PresheafOfModules.{u} (Spec (CommRingCat.of A)).ringCatSheaf.obj)

abbrev scalars := (AlgebraSheafScalars.presheaves A (ModuleScalars.base A)).obj M

variable (hM : ∀ a : A, IsLocalizedModule (Submonoid.powers a)
  ((scalars A M).map (PrimeSpectrum.basicOpen a).leTop.op).hom)

def baseIso : modulesSpecToSheaf.obj ((SchemeModuleSheafification.functor (Spec (CommRingCat.of A))).obj M) ≅
    modulesSpecToSheaf.obj (tilde ((scalars A M).obj (op ⊤))) :=
  (ModuleScalars.objectIso A _).symm ≪≫
    (AlgebraSheafificationScalars.objectIso A (ModuleScalars.base A) M).symm ≪≫
      Independent.LocalizingBasis.sheafIso (CommRingCat.of A) (scalars A M) hM

def iso : (SchemeModuleSheafification.functor (Spec (CommRingCat.of A))).obj M ≅
    tilde ((scalars A M).obj (op ⊤)) :=
  SpecModulesToSheafFullyFaithful.preimageIso (baseIso A M hM)

include hM in
theorem quasicoherent : ((SchemeModuleSheafification.functor (Spec (CommRingCat.of A))).obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of A)).ringCatSheaf).prop_of_iso (iso A M hM).symm
    (show (tilde (R := CommRingCat.of A) ((scalars A M).obj (op ⊤))).IsQuasicoherent from inferInstance)

def globalIso : (moduleSpecΓFunctor (R := CommRingCat.of A)).obj
    ((SchemeModuleSheafification.functor (Spec (CommRingCat.of A))).obj M) ≅
    (scalars A M).obj (op ⊤) :=
  (moduleSpecΓFunctor (R := CommRingCat.of A)).mapIso (iso A M hM) ≪≫
    (tilde.isoTop (R := CommRingCat.of A) _).symm

include hM in
theorem finite_generators [Module.Finite A ((scalars A M).obj (op ⊤))] :
    ∃ G : ((SchemeModuleSheafification.functor (Spec (CommRingCat.of A))).obj M).GeneratingSections,
      G.IsFiniteType := by
  let N := (SchemeModuleSheafification.functor (Spec (CommRingCat.of A))).obj M
  let V := (scalars A M).obj (op ⊤)
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := V)
  let ι := ULift.{u} (Fin r)
  let v : ι → V := fun i => s i.down
  have hv : Submodule.span A (Set.range v) = ⊤ := by
    have hr : Set.range v = Set.range s := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i.down, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨ULift.up i, rfl⟩
    rw [hr, hs]
  let f : ModuleCat.of A (ι →₀ A) ⟶ V :=
    ModuleCat.ofHom (X := ModuleCat.of A (ι →₀ A)) (Y := V) (Finsupp.linearCombination (M := V) A v)
  let : Epi f := (ModuleCat.epi_iff_surjective f).mpr
    ((span_range_eq_top_iff_surjective_finsuppLinearCombination A).mp hv)
  let : (tilde.functor (CommRingCat.of A)).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction tilde.adjunction
  let e := tildeFinsupp (R := CommRingCat.of A) ι
  let g : SheafOfModules.free (R := (Spec (CommRingCat.of A)).ringCatSheaf) ι ⟶ N :=
    e.inv ≫ (tilde.functor (CommRingCat.of A)).map f ≫ (iso A M hM).inv
  let : Epi g := by
    let : IsIso e.inv := e.isIso_inv
    let : IsIso (iso A M hM).inv := (iso A M hM).isIso_inv
    have hf : Epi ((tilde.functor (CommRingCat.of A)).map f) := Functor.map_epi _ f
    exact epi_comp' (IsIso.epi_of_iso e.inv) (epi_comp' hf (IsIso.epi_of_iso (iso A M hM).inv))
  let G : N.GeneratingSections :=
    { I := ι
      s := N.freeHomEquiv g
      epi := by rw [Equiv.symm_apply_apply]; infer_instance }
  exact ⟨G, ⟨inferInstanceAs (Finite ι)⟩⟩

include hM in
theorem finiteType [Module.Finite A ((scalars A M).obj (op ⊤))] :
    ((SchemeModuleSheafification.functor (Spec (CommRingCat.of A))).obj M).IsFiniteType := by
  obtain ⟨G, hG⟩ := finite_generators A M hM
  let : G.IsFiniteType := hG
  refine { exists_localGeneratorsData := ?_ }
  refine ⟨G.localGeneratorsData, ?_⟩
  constructor
  intro U
  exact ⟨hG.finite⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LocalizingModule
