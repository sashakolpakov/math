import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.ConeReferenceQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GlobalSectionTop
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.CechConeGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SectionCechNaturality

/-! # Open Cech Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.OpenCechQuasiIso.Global

noncomputable section

/-! The literal global-section restriction of the original bounded
crystalline injective resolution is a quasi-isomorphism onto its open
Čech total. The source is identified with top-open sections canonically. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))
  {C : Type v} [Category.{w} C] [HasBinaryProducts C] (F : C ⥤ Y.Opens)
  {ι : Type} [Finite ι] (U : ι → C)
  [∀ (q : ℕ) (t : Fin (q+1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "G" => OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.globalSections
  (p := p) (J := J) (δ := δ) fY n

def opens := BoundedOpen.SectionComplex.functor
  (p := p) (J := J) (δ := δ) fY n ⋙
    (Functor.whiskeringLeft Cᵒᵖ Y.Opensᵒᵖ (ModuleCat.{u+2} R)).obj F.op

instance opens_additive : (opens (p := p) (J := J) (δ := δ) fY n F).Additive := by
  dsimp only [opens]
  infer_instance

def restriction : G ⋙ Functor.const Cᵒᵖ ⟶ opens (p := p) (J := J) (δ := δ) fY n F :=
  Functor.whiskerRight (GeometricComparison.Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation
    (p := p) (J := J) (δ := δ) fY n)
    ((Functor.whiskeringLeft Cᵒᵖ Y.Opensᵒᵖ (ModuleCat.{u+2} R)).obj F.op)

def cone :
    ((Functor.const Cᵒᵖ).mapHomologicalComplex (.up ℕ)).obj
        (((G).mapHomologicalComplex (.up ℕ)).obj I.cocomplex) ⟶
      ((opens (p := p) (J := J) (δ := δ) fY n F).mapHomologicalComplex (.up ℕ)).obj I.cocomplex :=
  ((restriction (p := p) (J := J) (δ := δ) fY n F).mapHomologicalComplex (.up ℕ)).app I.cocomplex

omit [HasBinaryProducts C] in
theorem cone_eq : cone fY n I F =
    ((Functor.const Cᵒᵖ).mapHomologicalComplex (.up ℕ)).map
      (GlobalSectionTop.complexIso fY n I.cocomplex).hom ≫
        GeometricComparison.Bounded.CechConeGlobal.BoundedCechConeGlobalComparison.cone fY n I F := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext V
  exact (GlobalSectionTop.component fY n I.cocomplex q (F.obj V.unop)).symm

variable (hU : iSup (F.obj ∘ U) = ⊤)

include hU in
theorem quasiIso : QuasiIso (Presheaf.ConeQuasiIso.map.{v, w, u + 3, u + 2}
    (A := ModuleCat.{u+2} R)
    (M := ((G).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
    U (cone.{u, v, w} fY n I F)) := Presheaf.ConeReferenceQuasiIso.Reference.quasiIso.{v, w, u + 3, u + 2} U
  (cone fY n I F) (GeometricComparison.Bounded.CechConeGlobal.BoundedCechConeGlobalComparison.cone fY n I F)
  (GlobalSectionTop.complexIso fY n I.cocomplex) (cone_eq fY n I F)
  (GeometricComparison.Bounded.CechConeGlobal.BoundedCechConeGlobalComparison.quasiIso fY n I F U hU)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.OpenCechQuasiIso.Global
