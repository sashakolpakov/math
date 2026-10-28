import Mathlib.AlgebraicGeometry.Modules.Tilde
import OAI.NumberTheory.PadicHodge.GeometricComparison.LocalizedModule

/-! # Localizing Presheaf Sheaf -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LocalizingPresheafSheaf.LocalizingPresheafBasis

noncomputable section

/-! A presheaf whose principal restrictions localize its global module agrees on the principal basis with the associated module sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (A : CommRingCat.{u})

abbrev basisFunctor := inducedFunctor (fun a : A =>
  (PrimeSpectrum.basicOpen a : (Spec (A)).Opens))

variable (P : (Spec (A)).Opensᵒᵖ ⥤ ModuleCat.{u} A)
  (hP : ∀ a : A, IsLocalizedModule (Submonoid.powers a)
    (P.map (PrimeSpectrum.basicOpen a).leTop.op).hom)

abbrev associatedSheaf : Sheaf (Opens.grothendieckTopology (Spec (A))) (ModuleCat.{u} A) :=
  modulesSpecToSheaf.obj (tilde (R := A) (P.obj (op ⊤)))

include hP in
theorem componentIso_exists (a : A) :
    ∃ e : P.obj (op (PrimeSpectrum.basicOpen a)) ≅
      (associatedSheaf A P).obj.obj (op (PrimeSpectrum.basicOpen a)),
      P.map (PrimeSpectrum.basicOpen a).leTop.op ≫ e.hom =
        tilde.toOpen (R := A) (P.obj (op ⊤)) (PrimeSpectrum.basicOpen a) := by
  let := hP a
  exact LocalizedModule.LocalizedModuleIso.exists_iso A (Submonoid.powers a)
    (P.map (PrimeSpectrum.basicOpen a).leTop.op)
    (tilde.toOpen (R := A) (P.obj (op ⊤)) (PrimeSpectrum.basicOpen a))

def componentIso (a : A) : P.obj (op (PrimeSpectrum.basicOpen a)) ≅
    (associatedSheaf A P).obj.obj (op (PrimeSpectrum.basicOpen a)) :=
  (componentIso_exists A P hP a).choose

theorem componentIso_restriction (a : A) :
    P.map (PrimeSpectrum.basicOpen a).leTop.op ≫ (componentIso A P hP a).hom =
      tilde.toOpen (R := A) (P.obj (op ⊤)) (PrimeSpectrum.basicOpen a) :=
  (componentIso_exists A P hP a).choose_spec

theorem componentIso_naturality (a b : A)
    (f : (PrimeSpectrum.basicOpen b : (Spec (A)).Opens) ⟶
      PrimeSpectrum.basicOpen a) :
    P.map f.op ≫ (componentIso A P hP b).hom =
      (componentIso A P hP a).hom ≫ (associatedSheaf A P).obj.map f.op := by
  let := hP a
  apply ModuleCat.hom_ext
  apply IsLocalizedModule.ext (Submonoid.powers a)
    (P.map (PrimeSpectrum.basicOpen a).leTop.op).hom
  · rintro ⟨s, hs⟩
    obtain ⟨k, rfl⟩ := hs
    change IsUnit ((algebraMap A (Module.End A _)) (a ^ k))
    rw [map_pow]
    exact ((tilde (R := A) (P.obj (op ⊤))).isUnit_algebraMap_end_of_le_basicOpen
      a (leOfHom f)).pow k
  · apply ModuleCat.hom_ext_iff.mp
    change P.map (PrimeSpectrum.basicOpen a).leTop.op ≫
        (P.map f.op ≫ (componentIso A P hP b).hom) =
      P.map (PrimeSpectrum.basicOpen a).leTop.op ≫
        ((componentIso A P hP a).hom ≫ (associatedSheaf A P).obj.map f.op)
    have ht : P.map (PrimeSpectrum.basicOpen a).leTop.op ≫ P.map f.op =
        P.map (PrimeSpectrum.basicOpen b).leTop.op :=
      (P.map_comp _ _).symm.trans (congrArg P.map (Subsingleton.elim _ _))
    have hl : P.map (PrimeSpectrum.basicOpen a).leTop.op ≫
        (P.map f.op ≫ (componentIso A P hP b).hom) =
        tilde.toOpen (R := A) (P.obj (op ⊤)) (PrimeSpectrum.basicOpen b) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun m => m ≫ (componentIso A P hP b).hom) ht).trans
          (componentIso_restriction A P hP b))
    have hr : P.map (PrimeSpectrum.basicOpen a).leTop.op ≫
        ((componentIso A P hP a).hom ≫ (associatedSheaf A P).obj.map f.op) =
        tilde.toOpen (R := A) (P.obj (op ⊤)) (PrimeSpectrum.basicOpen b) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun m => m ≫ (associatedSheaf A P).obj.map f.op)
          (componentIso_restriction A P hP a)).trans
            (tilde.toOpen_res (R := A) (P.obj (op ⊤)) _ _ f))
    exact hl.trans hr.symm

def iso : (basisFunctor A).op ⋙ P ≅
    (basisFunctor A).op ⋙ (associatedSheaf A P).obj :=
  NatIso.ofComponents (fun a => componentIso A P hP a.unop)
    (fun {a b} f => componentIso_naturality A P hP a.unop b.unop f.unop.hom)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LocalizingPresheafSheaf.LocalizingPresheafBasis
