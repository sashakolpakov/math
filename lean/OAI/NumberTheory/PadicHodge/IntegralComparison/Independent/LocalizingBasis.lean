import OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.BasisSheafification
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Localizing Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.LocalizingBasis

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

universe u

section ModuleLift

variable {R : Type u} [CommRing R] {M N Q : ModuleCat.{u} R}

def localizationLift (S : Submonoid R) (f : M ⟶ N) (hf : IsLocalizedModule S f.hom)
    (g : M ⟶ Q) (hg : ∀ s : S, IsUnit (algebraMap R (Module.End R Q) s)) : N ⟶ Q := by
  let : IsLocalizedModule S f.hom := hf
  exact ModuleCat.ofHom (IsLocalizedModule.lift S f.hom g.hom hg)

theorem localizationLift_fac (S : Submonoid R) (f : M ⟶ N) (hf : IsLocalizedModule S f.hom)
    (g : M ⟶ Q) (hg : ∀ s : S, IsUnit (algebraMap R (Module.End R Q) s)) :
    f ≫ localizationLift S f hf g hg = g := by
  let : IsLocalizedModule S f.hom := hf
  apply ModuleCat.hom_ext
  exact LinearMap.ext (fun x => IsLocalizedModule.lift_apply S f.hom g.hom hg x)

end ModuleLift

variable (A : CommRingCat.{u}) (P : (Spec A).Opensᵒᵖ ⥤ ModuleCat.{u} A)

abbrev basicOpen (a : A) : (Spec A).Opens := PrimeSpectrum.basicOpen a

abbrev associatedSheaf : Sheaf (Opens.grothendieckTopology (Spec A)) (ModuleCat.{u} A) :=
  modulesSpecToSheaf.obj (tilde (R := A) (P.obj (op ⊤)))

theorem powers_units (a : A) (V : (Spec A).Opens) (hV : V ≤ LocalizingBasis.basicOpen A a) :
    ∀ s : Submonoid.powers a,
      IsUnit (algebraMap A (Module.End A ((associatedSheaf A P).obj.obj (op V))) s) := by
  rw [Subtype.forall]
  change Submonoid.powers a ≤ (IsUnit.submonoid _).comap _
  simp only [Submonoid.powers_le, Submonoid.mem_comap]
  exact (tilde (R := A) (P.obj (op ⊤))).isUnit_algebraMap_end_of_le_basicOpen a hV

variable (hP : ∀ a : A, IsLocalizedModule (Submonoid.powers a)
  (P.map (LocalizingBasis.basicOpen A a).leTop.op).hom)

def component (a : A) : P.obj (op (LocalizingBasis.basicOpen A a)) ⟶
    (associatedSheaf A P).obj.obj (op (LocalizingBasis.basicOpen A a)) :=
  localizationLift (Submonoid.powers a) (P.map (LocalizingBasis.basicOpen A a).leTop.op) (hP a)
    (tilde.toOpen (R := A) (P.obj (op ⊤)) (LocalizingBasis.basicOpen A a))
    (powers_units A P a (LocalizingBasis.basicOpen A a) le_rfl)

theorem component_fac (a : A) :
    P.map (LocalizingBasis.basicOpen A a).leTop.op ≫ component A P hP a =
      tilde.toOpen (R := A) (P.obj (op ⊤)) (LocalizingBasis.basicOpen A a) :=
  localizationLift_fac (Submonoid.powers a) (P.map (LocalizingBasis.basicOpen A a).leTop.op) (hP a)
    (tilde.toOpen (R := A) (P.obj (op ⊤)) (LocalizingBasis.basicOpen A a))
    (powers_units A P a (LocalizingBasis.basicOpen A a) le_rfl)

include hP in
theorem component_isIso (a : A) : IsIso (component A P hP a) := by
  refine ModuleCat.isIso_of_isLocalizedModule_comp (hP a) ?_
  rw [component_fac]
  infer_instance

def basisMap :
    (inducedFunctor (fun a : A => (LocalizingBasis.basicOpen A a : (Spec A).Opens))).op ⋙ P ⟶
    (inducedFunctor (fun a : A => (LocalizingBasis.basicOpen A a : (Spec A).Opens))).op ⋙
      (associatedSheaf A P).obj where
  app (a : Aᵒᵖ) := component A P hP a.unop
  naturality {a b : Aᵒᵖ} i := by
    let : IsLocalizedModule (Submonoid.powers a.unop)
      (P.map (LocalizingBasis.basicOpen A a.unop).leTop.op).hom := hP a.unop
    apply ModuleCat.hom_ext
    apply IsLocalizedModule.ext (Submonoid.powers a.unop)
      (P.map (LocalizingBasis.basicOpen A a.unop).leTop.op).hom
    · exact powers_units A P a.unop (LocalizingBasis.basicOpen A b.unop) i.1.hom.le
    · let q := (inducedFunctor (fun a : A => (LocalizingBasis.basicOpen A a : (Spec A).Opens))).op.map i
      change ((P.map (LocalizingBasis.basicOpen A a.unop).leTop.op ≫ P.map q) ≫
          component A P hP b.unop).hom =
        ((P.map (LocalizingBasis.basicOpen A a.unop).leTop.op ≫ component A P hP a.unop) ≫
          (associatedSheaf A P).obj.map q).hom
      congr 1
      have hq : (LocalizingBasis.basicOpen A a.unop).leTop.op ≫ q =
          (LocalizingBasis.basicOpen A b.unop).leTop.op := Subsingleton.elim _ _
      calc
        (P.map (LocalizingBasis.basicOpen A a.unop).leTop.op ≫ P.map q) ≫ component A P hP b.unop =
            P.map ((LocalizingBasis.basicOpen A a.unop).leTop.op ≫ q) ≫ component A P hP b.unop :=
          congrArg (fun t => t ≫ component A P hP b.unop) (P.map_comp _ _).symm
        _ = P.map (LocalizingBasis.basicOpen A b.unop).leTop.op ≫ component A P hP b.unop := by rw [hq]
        _ = tilde.toOpen (R := A) (P.obj (op ⊤)) (LocalizingBasis.basicOpen A b.unop) := component_fac A P hP b.unop
        _ = tilde.toOpen (R := A) (P.obj (op ⊤)) (LocalizingBasis.basicOpen A a.unop) ≫
            (associatedSheaf A P).obj.map q :=
          (tilde.toOpen_res (R := A) (P.obj (op ⊤)) _ _ q.unop).symm
        _ = (P.map (LocalizingBasis.basicOpen A a.unop).leTop.op ≫ component A P hP a.unop) ≫
            (associatedSheaf A P).obj.map q :=
          congrArg (fun t => t ≫ (associatedSheaf A P).obj.map q) (component_fac A P hP a.unop).symm

def iso :
    (inducedFunctor (fun a : A => (LocalizingBasis.basicOpen A a : (Spec A).Opens))).op ⋙ P ≅
    (inducedFunctor (fun a : A => (LocalizingBasis.basicOpen A a : (Spec A).Opens))).op ⋙
      (associatedSheaf A P).obj :=
  NatIso.ofComponents (fun (a : Aᵒᵖ) => by
    let : IsIso (component A P hP a.unop) := component_isIso A P hP a.unop
    exact asIso (component A P hP a.unop))
    (fun i => (basisMap A P hP).naturality i)

def sheafIso : (presheafToSheaf (Opens.grothendieckTopology (Spec A)) (ModuleCat.{u} A)).obj P ≅
    associatedSheaf A P :=
  BasisSheafification.iso
    (fun a : A => (LocalizingBasis.basicOpen A a : (Spec A).Opens))
    PrimeSpectrum.isBasis_basic_opens P (associatedSheaf A P) (iso A P hP)

include hP in
theorem unit_principal_isIso (a : A) :
    IsIso ((toSheafify (Opens.grothendieckTopology (Spec A)) P).app (op (LocalizingBasis.basicOpen A a))) :=
  BasisSheafification.unit_isIso
    (fun a : A => (LocalizingBasis.basicOpen A a : (Spec A).Opens))
    PrimeSpectrum.isBasis_basic_opens P (associatedSheaf A P) (iso A P hP) a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.LocalizingBasis
