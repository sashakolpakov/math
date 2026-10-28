import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SinglePresheafCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.SingleGlobalCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.Presheaf

/-! # Single Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.SingleCoordinates.Reference

noncomputable section

/-! The actual original-cover transfer on a module in one degree
retains the original principal and native global single-coordinate
isomorphisms. Its coefficient map is the literal unshifted comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

private theorem isIso_of_square {C : Type*} [Category* C]
    {A B A' B' : C} (a : A ⟶ B) (b : A' ⟶ B') (e : A ≅ A') (f : B ≅ B')
    [IsIso a] (h : a ≫ f.hom = e.hom ≫ b) : IsIso b := by
  have hb : b = e.inv ≫ a ≫ f.hom := by rw [h, Iso.inv_hom_id_assoc]
  rw [hb]
  infer_instance

private theorem paste {Cat : Type*} [Category Cat] {A B C D E F G : Cat}
    {lo : A ⟶ B} {ct : B ⟶ D} {oc : A ⟶ C} {ch : C ⟶ D}
    {ls : B ⟶ E} {ts : D ⟶ F} {cc : E ⟶ F} {cf : F ⟶ G} {ng : C ⟶ G}
    (hn : lo ≫ ct = oc ≫ ch) (hs : ct ≫ ts = ls ≫ cc)
    (hg : ch ≫ ts ≫ cf = ng) :
    oc ≫ ng = (lo ≫ ls) ≫ (cc ≫ cf) := by
  rw [← hg, ← Category.assoc oc ch, ← hn]
  simp only [Category.assoc]
  rw [← Category.assoc ct ts, hs]
  simp only [Category.assoc]

open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeConcentration
variable {X Z : Scheme.{u}} [X.IsSeparated] (U : X.Opens) (hU : IsAffineOpen U)
  {ι κ ν : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (W : ι → Principal.SectionPresheaf.Index U) (f : Z ⟶ X) [IsClosedImmersion f] (hfU : ⊤ ≤ f ⁻¹ᵁ U)
  (J : ν → X.Opens)
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι (Principal.RelativeConcentration.family U hU W))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk
    (ComplementaryAffineCover.Index (SectionIdealPuncturedCover.outside f.ker))
    (ComplementaryAffineCover.opens (SectionIdealPuncturedCover.outside f.ker)))
  (V : κ → X.Opens) (hV : iSup V = ⊤) (haV : ∀ i, IsAffineOpen (V i))
  (N : X.Modules) [N.IsQuasicoherent] (c g q : ℕ) (hq : q=g+c)

local instance single_qc (n : ℕ) :
    ((Reference.SinglePresheafCoordinates.moduleSingle N c).X n).IsQuasicoherent :=
  QuasicoherentTruncation.single N c n

private abbrev complement :=
  ComplementaryAffineCover.opens (SectionIdealPuncturedCover.outside f.ker)
private abbrev common := PointComplementGlobalCover.common f (Principal.RelativeConcentration.ambient U hU) V
private abbrev left := PointComplementGlobalCover.left f (Principal.RelativeConcentration.ambient U hU) V
private abbrev right := PointComplementGlobalCover.right f (Principal.RelativeConcentration.ambient U hU) V

private def relativeChangeIso {τ : Type u} [LinearOrder τ] (A : τ → X.Opens) :=
  homologyMapIso (HomologicalComplex₂.total.mapIso
    (((RelativeCech.Total.localFunctor (Principal.RelativeConcentration.ambient U hU) A).mapHomologicalComplex (.up ℕ)).mapIso
      (Reference.SinglePresheafCoordinates.iso N c)) (.up ℕ)) q

variable [IsIso (RelativeCech.Refinement.homology (Principal.RelativeConcentration.ambient U hU) (complement f) J s
  (Relative.AdditiveCechConcentration.coefficients
    (Reference.SinglePresheafCoordinates.moduleSingle N c)) q)]

omit [X.IsSeparated] [IsClosedImmersion f] [N.IsQuasicoherent] in
private theorem relative_isIso :
    IsIso (RelativeCech.Refinement.homology (Principal.RelativeConcentration.ambient U hU) (complement f) J s
      ((single (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (.up ℕ) c).obj
        (Reference.SinglePresheafCoordinates.presheaf N)) q) :=
  isIso_of_square _ _ (relativeChangeIso U hU N c q (complement f))
    (relativeChangeIso U hU N c q J)
    (RelativeCech.Refinement.homology_naturality (Principal.RelativeConcentration.ambient U hU) (complement f) J s
      (Reference.SinglePresheafCoordinates.iso N c).hom q).symm

include hfU hV haV in
private theorem old_global_isIso :
    IsIso (homologyMap (OrderedCech.Refinement.totalMap V (common U hU f V) (right U hU f V)
      (Relative.AdditiveCechConcentration.coefficients
        (Reference.SinglePresheafCoordinates.moduleSingle N c))) q) :=
  Additive.OrderedCoverRefinement.homology_isIso V (common U hU f V) (right U hU f V) hV
    (PointComplementGlobalCover.common_covers f (Principal.RelativeConcentration.ambient U hU)
      (CoverTransfer.Reference.contains U hU f hfU) V hV)
    haV (PointComplementGlobalCover.common_affine f (Principal.RelativeConcentration.ambient U hU)
      (Principal.RelativeConcentration.ambient_affine U hU) V haV) (Reference.SinglePresheafCoordinates.moduleSingle N c) q

include hfU hV haV in
private theorem global_isIso :
    IsIso (homologyMap (OrderedCech.Refinement.totalMap V (common U hU f V) (right U hU f V)
      ((single (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (.up ℕ) c).obj
        (Reference.SinglePresheafCoordinates.presheaf N))) q) := by
  let := old_global_isIso U hU f hfU V hV haV N c q
  exact isIso_of_square _ _
    (homologyMapIso (Reference.SingleGlobalCoordinates.changeIso V N c) q)
    (homologyMapIso (Reference.SingleGlobalCoordinates.changeIso (common U hU f V) N c) q)
    (Presheaf.OrderedCover.Comparison.homology_naturality V (common U hU f V) (right U hU f V)
      (Reference.SinglePresheafCoordinates.iso N c).hom q).symm

def coefficientComparison := by
  letI := relative_isIso U hU f J s N c q
  letI := global_isIso U hU f hfU V hV haV N c q
  exact Principal.PresheafSingleIndexedCoordinates.coefficientComparison
    (Reference.SinglePresheafCoordinates.presheaf N) c g
    (Principal.AdditiveSections.opens U hU) W (complement f) J r s
    V (common U hU f V) (left U hU f V) (right U hU f V) q hq ≫
      (IntrinsicOrdered.SingleAdditiveCoordinates.Intrinsic.coefficientIso (𝟙 X) V N g).inv

theorem comparison :
    CoverTransfer.Reference.comparison U hU W f hfU J r s V hV haV
      (K := Reference.SinglePresheafCoordinates.moduleSingle N c) q ≫
      (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso (𝟙 X) V
        (Reference.SinglePresheafCoordinates.moduleSingle N c) q).inv ≫
      (Global.PureIndexedCoordinates.singleIso (𝟙 X) V N c g q hq).hom =
    (Principal.SinglePresheafCoordinates.coordinates U hU N c W g q hq).hom ≫
      coefficientComparison U hU W f hfU J r s V hV haV N c g q hq := by
  let := relative_isIso U hU f J s N c q
  let := global_isIso U hU f hfU V hV haV N c q
  have hn := Presheaf.ReferenceComparison.naturality U hU W f hfU J r s V hV haV
    (Reference.SinglePresheafCoordinates.moduleSingle N c) q
    ((single (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (.up ℕ) c).obj
      (Reference.SinglePresheafCoordinates.presheaf N))
    (Reference.SinglePresheafCoordinates.iso N c).hom
  rw [← Category.assoc, Principal.SinglePresheafCoordinates.factor] at hn
  exact paste hn
    (Principal.PresheafSingleIndexedCoordinates.comparison
      (Reference.SinglePresheafCoordinates.presheaf N) c g
      (Principal.AdditiveSections.opens U hU) W (complement f) J r s
      V (common U hU f V) (left U hU f V) (right U hU f V) q hq)
    (Reference.SingleGlobalCoordinates.inverse (𝟙 X) V N c g q hq)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.SingleCoordinates.Reference
