import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LineIsoRatios
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.CompositionForward
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationDefect
import OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedDefectUnitLaws
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CocycleSquareSymmetry

/-! # Line Translation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LineTranslation.PoincareBundle

noncomputable section

/-! Tensoring the actual translation action squares its scalar defect.
For an involutive kernel, the normalized squared action has symmetric defect. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj
universe u v w
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CocycleSquareSymmetry OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback
open OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationFibers

private theorem composeIsoComparison {C : Type v} [Category.{w} C]
    {A B C₀ D E F G : C} (P : A ≅ B) (Q : B ≅ C₀)
    (c : C₀ ≅ D) (d : D ≅ E) (ct : A ≅ F) (R : F ≅ D)
    (dt : F ≅ G) (e : G ≅ E) (cd : C₀ ≅ E)
    (hc : P ≪≫ Q ≪≫ c = ct ≪≫ R) (hd : dt ≪≫ e = R ≪≫ d)
    (hcd : cd = c ≪≫ d) : P ≪≫ Q ≪≫ cd = (ct ≪≫ dt) ≪≫ e := by
  calc
    _ = P ≪≫ Q ≪≫ (c ≪≫ d) := congrArg (fun k => P ≪≫ Q ≪≫ k) hcd
    _ = (P ≪≫ Q ≪≫ c) ≪≫ d := by simp only [Iso.trans_assoc]
    _ = (ct ≪≫ R) ≪≫ d := congrArg (fun k => k ≪≫ d) hc
    _ = ct ≪≫ (R ≪≫ d) := Iso.trans_assoc _ _ _
    _ = ct ≪≫ (dt ≪≫ e) := congrArg (fun k => ct ≪≫ k) hd.symm
    _ = _ := (Iso.trans_assoc _ _ _).symm

section Fibers
variable {S : Scheme.{u}} {A : Over S} (L : Picard.PoincareBundle.Line.Bundles.LineBundle A.left)

def fiberTensorIso {T : Over S} (x : T ⟶ A) :
    Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Tensor.LineBundles.tensor L L) x ≅
      ProductSheaf.tensorModule (Picard.PoincareBundle.Line.Fibers.fiber L x) (Picard.PoincareBundle.Line.Fibers.fiber L x) :=
  Picard.PoincareBundle.Tensor.LinePullback.pullbackIso x.left L.sheaf L.sheaf L.isLine L.isLine

theorem fiberTensorIso_comparison {T U : Over S} (q : U ⟶ T)
    (x : T ⟶ A) (x' : U ⟶ A) (hx : q ≫ x = x') :
    (Scheme.Modules.pullback q.left).mapIso (fiberTensorIso L x) ≪≫
      Picard.PoincareBundle.Tensor.LinePullback.pullbackIso q.left (Picard.PoincareBundle.Line.Fibers.fiber L x) (Picard.PoincareBundle.Line.Fibers.fiber L x) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L x) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L x) ≪≫
      ProductSheaf.tensorModuleCongr (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L q x x' hx) (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L q x x' hx) =
    Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Picard.PoincareBundle.Tensor.LineBundles.tensor L L) q x x' hx ≪≫ fiberTensorIso L x' := by
  let c := (Scheme.Modules.pullbackComp q.left x.left).app L.sheaf
  let ct := (Scheme.Modules.pullbackComp q.left x.left).app (ProductSheaf.tensorModule L.sheaf L.sheaf)
  let d := (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hx)).app L.sheaf
  let dt := (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hx)).app
    (ProductSheaf.tensorModule L.sheaf L.sheaf)
  let R := Picard.PoincareBundle.Tensor.LinePullback.pullbackIso (q.left ≫ x.left) L.sheaf L.sheaf L.isLine L.isLine
  let P := (Scheme.Modules.pullback q.left).mapIso (fiberTensorIso L x)
  let Q := Picard.PoincareBundle.Tensor.LinePullback.pullbackIso q.left (Picard.PoincareBundle.Line.Fibers.fiber L x) (Picard.PoincareBundle.Line.Fibers.fiber L x) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L x) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L x)
  have hc : P ≪≫ Q ≪≫ ProductSheaf.tensorModuleCongr c c = ct ≪≫ R :=
    Picard.PoincareBundle.Tensor.CompositionForward.composition q.left x.left L.sheaf L.sheaf L.isLine L.isLine
  have hd : dt ≪≫ fiberTensorIso L x' = R ≪≫ ProductSheaf.tensorModuleCongr d d :=
    Picard.PoincareBundle.Tensor.LineIsoCoherence.congr_map (q.left ≫ x.left)
      (congrArg Over.Hom.left hx) L.sheaf L.sheaf L.isLine L.isLine
  change P ≪≫ Q ≪≫ ProductSheaf.tensorModuleCongr (c ≪≫ d) (c ≪≫ d) =
    (ct ≪≫ dt) ≪≫ fiberTensorIso L x'
  exact composeIsoComparison P Q (ProductSheaf.tensorModuleCongr c c) (ProductSheaf.tensorModuleCongr d d)
    ct R dt (fiberTensorIso L x') (ProductSheaf.tensorModuleCongr (c ≪≫ d) (c ≪≫ d))
    hc hd (Picard.PoincareBundle.Tensor.CongrComposition.trans c c d d).symm
end Fibers

section Transport
variable {S : Scheme.{u}} {H A : Over S} [GrpObj A]
  (i : H ⟶ A) (L : Picard.PoincareBundle.Line.Bundles.LineBundle A.left)
  (t : Picard.PoincareBundle.Line.Fibers.fiber L (snd H A) ≅ Picard.PoincareBundle.Line.Fibers.fiber L (Picard.PoincareBundle.NormalizedKernelTranslation.action i))

def tensorTranslation :
    Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Tensor.LineBundles.tensor L L) (snd H A) ≅
      Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Tensor.LineBundles.tensor L L) (Picard.PoincareBundle.NormalizedKernelTranslation.action i) :=
  fiberTensorIso L (snd H A) ≪≫ ProductSheaf.tensorModuleCongr t t ≪≫ (fiberTensorIso L (Picard.PoincareBundle.NormalizedKernelTranslation.action i)).symm

theorem transportIso_tensorTranslation {T : Over S}
    (x y : T ⟶ A) (a : T ⟶ H) (h : (a ≫ i) * x = y) :
    Picard.PoincareBundle.Subgroup.TranslationFibers.transportIso i (Picard.PoincareBundle.Tensor.LineBundles.tensor L L) (tensorTranslation i L t) x y a h =
      fiberTensorIso L x ≪≫
        ProductSheaf.tensorModuleCongr (Picard.PoincareBundle.Subgroup.TranslationFibers.transportIso i L t x y a h) (Picard.PoincareBundle.Subgroup.TranslationFibers.transportIso i L t x y a h) ≪≫
          (fiberTensorIso L y).symm := by
  let q : T ⟶ H ⊗ A := lift a x
  let hx : q ≫ snd H A = x := lift_snd a x
  let hy : q ≫ Picard.PoincareBundle.NormalizedKernelTranslation.action i = y := (Picard.PoincareBundle.Subgroup.TranslationFibers.action_pair i a x).trans h
  let F := Scheme.Modules.pullback q.left
  let sx := Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L q (snd H A) x hx
  let sy := Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L q (Picard.PoincareBundle.NormalizedKernelTranslation.action i) y hy
  let sx₂ := Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Picard.PoincareBundle.Tensor.LineBundles.tensor L L) q (snd H A) x hx
  let sy₂ := Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Picard.PoincareBundle.Tensor.LineBundles.tensor L L) q (Picard.PoincareBundle.NormalizedKernelTranslation.action i) y hy
  let C₀ := fiberTensorIso L (snd H A)
  let C₁ := fiberTensorIso L (Picard.PoincareBundle.NormalizedKernelTranslation.action i)
  let Cx := fiberTensorIso L x
  let Cy := fiberTensorIso L y
  let D₀ := Picard.PoincareBundle.Tensor.LinePullback.pullbackIso q.left (Picard.PoincareBundle.Line.Fibers.fiber L (snd H A)) (Picard.PoincareBundle.Line.Fibers.fiber L (snd H A))
    (Picard.PoincareBundle.Line.Fibers.fiber_isLine L (snd H A)) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L (snd H A))
  let D₁ := Picard.PoincareBundle.Tensor.LinePullback.pullbackIso q.left (Picard.PoincareBundle.Line.Fibers.fiber L (Picard.PoincareBundle.NormalizedKernelTranslation.action i)) (Picard.PoincareBundle.Line.Fibers.fiber L (Picard.PoincareBundle.NormalizedKernelTranslation.action i))
    (Picard.PoincareBundle.Line.Fibers.fiber_isLine L (Picard.PoincareBundle.NormalizedKernelTranslation.action i)) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L (Picard.PoincareBundle.NormalizedKernelTranslation.action i))
  have hsrc : F.mapIso C₀ ≪≫ D₀ ≪≫ ProductSheaf.tensorModuleCongr sx sx = sx₂ ≪≫ Cx :=
    fiberTensorIso_comparison L q (snd H A) x hx
  have htar : F.mapIso C₁ ≪≫ D₁ ≪≫ ProductSheaf.tensorModuleCongr sy sy = sy₂ ≪≫ Cy :=
    fiberTensorIso_comparison L q (Picard.PoincareBundle.NormalizedKernelTranslation.action i) y hy
  have hnat : F.mapIso (ProductSheaf.tensorModuleCongr t t) ≪≫ D₁ =
      D₀ ≪≫ ProductSheaf.tensorModuleCongr (F.mapIso t) (F.mapIso t) :=
    Picard.PoincareBundle.Tensor.LineIsoCoherence.naturality q.left
      (Picard.PoincareBundle.Line.Fibers.fiber_isLine L (snd H A)) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L (Picard.PoincareBundle.NormalizedKernelTranslation.action i))
      (Picard.PoincareBundle.Line.Fibers.fiber_isLine L (snd H A)) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L (Picard.PoincareBundle.NormalizedKernelTranslation.action i)) t t
  have hs : sx₂.symm ≪≫ F.mapIso C₀ ≪≫ D₀ =
      Cx ≪≫ (ProductSheaf.tensorModuleCongr sx sx).symm := by
    have he := congrArg
      (fun e => sx₂.symm ≪≫ e ≪≫ (ProductSheaf.tensorModuleCongr sx sx).symm) hsrc
    simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id_assoc,
      Iso.symm_self_id, Iso.self_symm_id, Iso.refl_trans, Iso.trans_refl] using he
  have ht : (F.mapIso C₁).symm ≪≫ sy₂ =
      D₁ ≪≫ ProductSheaf.tensorModuleCongr sy sy ≪≫ Cy.symm := by
    have he := congrArg (fun e => (F.mapIso C₁).symm ≪≫ e ≪≫ Cy.symm) htar
    simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id_assoc,
      Iso.symm_self_id, Iso.self_symm_id, Iso.refl_trans, Iso.trans_refl] using he.symm
  have hinv : (ProductSheaf.tensorModuleCongr sx sx).symm = ProductSheaf.tensorModuleCongr sx.symm sx.symm := by
    apply Iso.ext
    rfl
  have hmul : (ProductSheaf.tensorModuleCongr sx sx).symm ≪≫
      ProductSheaf.tensorModuleCongr (F.mapIso t) (F.mapIso t) ≪≫ ProductSheaf.tensorModuleCongr sy sy =
      ProductSheaf.tensorModuleCongr (sx.symm ≪≫ F.mapIso t ≪≫ sy) (sx.symm ≪≫ F.mapIso t ≪≫ sy) := by
    rw [hinv, Picard.PoincareBundle.Tensor.CongrComposition.trans, Picard.PoincareBundle.Tensor.CongrComposition.trans]
  change sx₂.symm ≪≫ F.mapIso (tensorTranslation i L t) ≪≫ sy₂ =
    Cx ≪≫ ProductSheaf.tensorModuleCongr (sx.symm ≪≫ F.mapIso t ≪≫ sy)
      (sx.symm ≪≫ F.mapIso t ≪≫ sy) ≪≫ Cy.symm
  calc
    _ = sx₂.symm ≪≫ F.mapIso C₀ ≪≫ F.mapIso (ProductSheaf.tensorModuleCongr t t) ≪≫
        (F.mapIso C₁).symm ≪≫ sy₂ := by
      change sx₂.symm ≪≫ F.mapIso (C₀ ≪≫ ProductSheaf.tensorModuleCongr t t ≪≫ C₁.symm) ≪≫ sy₂ = _
      simp only [Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_assoc]
    _ = sx₂.symm ≪≫ F.mapIso C₀ ≪≫ F.mapIso (ProductSheaf.tensorModuleCongr t t) ≪≫
        D₁ ≪≫ ProductSheaf.tensorModuleCongr sy sy ≪≫ Cy.symm := by rw [ht]
    _ = sx₂.symm ≪≫ F.mapIso C₀ ≪≫ (F.mapIso (ProductSheaf.tensorModuleCongr t t) ≪≫ D₁) ≪≫
        ProductSheaf.tensorModuleCongr sy sy ≪≫ Cy.symm := by simp only [Iso.trans_assoc]
    _ = sx₂.symm ≪≫ F.mapIso C₀ ≪≫ (D₀ ≪≫ ProductSheaf.tensorModuleCongr (F.mapIso t) (F.mapIso t)) ≪≫
        ProductSheaf.tensorModuleCongr sy sy ≪≫ Cy.symm :=
      congrArg (fun e => sx₂.symm ≪≫ F.mapIso C₀ ≪≫ e ≪≫ ProductSheaf.tensorModuleCongr sy sy ≪≫ Cy.symm) hnat
    _ = (sx₂.symm ≪≫ F.mapIso C₀ ≪≫ D₀) ≪≫
        ProductSheaf.tensorModuleCongr (F.mapIso t) (F.mapIso t) ≪≫ ProductSheaf.tensorModuleCongr sy sy ≪≫ Cy.symm := by
      simp only [Iso.trans_assoc]
    _ = (Cx ≪≫ (ProductSheaf.tensorModuleCongr sx sx).symm) ≪≫
        ProductSheaf.tensorModuleCongr (F.mapIso t) (F.mapIso t) ≪≫ ProductSheaf.tensorModuleCongr sy sy ≪≫ Cy.symm :=
      congrArg (fun e => e ≪≫ ProductSheaf.tensorModuleCongr (F.mapIso t) (F.mapIso t) ≪≫
        ProductSheaf.tensorModuleCongr sy sy ≪≫ Cy.symm) hs
    _ = Cx ≪≫ ((ProductSheaf.tensorModuleCongr sx sx).symm ≪≫
        ProductSheaf.tensorModuleCongr (F.mapIso t) (F.mapIso t) ≪≫ ProductSheaf.tensorModuleCongr sy sy) ≪≫ Cy.symm := by
      simp only [Iso.trans_assoc]
    _ = _ := congrArg (fun e => Cx ≪≫ e ≪≫ Cy.symm) hmul
end Transport

private theorem ratio_tensor_square_conjugate
    {X : Scheme.{u}} {M N P Q : X.Modules}
    (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) (hP : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle P)
    (c : P ≅ ProductSheaf.tensorModule M M) (d : Q ≅ ProductSheaf.tensorModule N N) (e f : M ≅ N) :
    Picard.PoincareBundle.Line.IsoRatios.ratio hP
      (c ≪≫ ProductSheaf.tensorModuleCongr e e ≪≫ d.symm)
      (c ≪≫ ProductSheaf.tensorModuleCongr f f ≪≫ d.symm) =
        Picard.PoincareBundle.Line.IsoRatios.ratio hM e f ^ 2 := by
  rw [← Iso.trans_assoc, ← Iso.trans_assoc, Picard.PoincareBundle.Line.IsoRatios.ratio_postcomp]
  rw [Picard.PoincareBundle.Line.IsoRatios.ratio_precomp
    (Picard.PoincareBundle.Tensor.LineBundles.tensor_isLine hM hM) hP c]
  rw [LineIsoRatios.PoincareBundle.ratio_tensor, pow_two]

section Defects
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberIsomorphismRatios OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.IsoRatios
variable {S : Scheme.{u}} {H A : Over S} [GrpObj A]
  (i : H ⟶ A) (L : Picard.PoincareBundle.Line.Bundles.LineBundle A.left)
  (t : Picard.PoincareBundle.Line.Fibers.fiber L (snd H A) ≅ Picard.PoincareBundle.Line.Fibers.fiber L (Picard.PoincareBundle.NormalizedKernelTranslation.action i))

theorem defect_tensorTranslation {T : Over S}
    (x y z : T ⟶ A) (a b c : T ⟶ H)
    (hx : (a ≫ i) * x = y) (hy : (b ≫ i) * y = z) (hz : (c ≫ i) * x = z) :
    Picard.PoincareBundle.Subgroup.TranslationDefect.defect i (Picard.PoincareBundle.Tensor.LineBundles.tensor L L)
      (tensorTranslation i L t) x y z a b c hx hy hz =
        Picard.PoincareBundle.Subgroup.TranslationDefect.defect i L t x y z a b c hx hy hz ^ 2 := by
  let e := Picard.PoincareBundle.Subgroup.TranslationFibers.transportIso i L t x y a hx
  let f := Picard.PoincareBundle.Subgroup.TranslationFibers.transportIso i L t y z b hy
  let g := Picard.PoincareBundle.Subgroup.TranslationFibers.transportIso i L t x z c hz
  have hc :
      Picard.PoincareBundle.Subgroup.TranslationFibers.transportIso i (Picard.PoincareBundle.Tensor.LineBundles.tensor L L) (tensorTranslation i L t) x y a hx ≪≫
        Picard.PoincareBundle.Subgroup.TranslationFibers.transportIso i (Picard.PoincareBundle.Tensor.LineBundles.tensor L L) (tensorTranslation i L t) y z b hy =
      fiberTensorIso L x ≪≫ ProductSheaf.tensorModuleCongr (e ≪≫ f) (e ≪≫ f) ≪≫
        (fiberTensorIso L z).symm := by
    simp only [transportIso_tensorTranslation, Iso.trans_assoc, Iso.symm_self_id_assoc]
    change fiberTensorIso L x ≪≫ ProductSheaf.tensorModuleCongr e e ≪≫ ProductSheaf.tensorModuleCongr f f ≪≫
        (fiberTensorIso L z).symm =
      fiberTensorIso L x ≪≫ ProductSheaf.tensorModuleCongr (e ≪≫ f) (e ≪≫ f) ≪≫ (fiberTensorIso L z).symm
    rw [← Iso.trans_assoc (ProductSheaf.tensorModuleCongr e e) (ProductSheaf.tensorModuleCongr f f)
      (fiberTensorIso L z).symm, Picard.PoincareBundle.Tensor.CongrComposition.trans]
  change Picard.PoincareBundle.Line.IsoRatios.ratio (Picard.PoincareBundle.FiberIsomorphismRatios.fiberLine (Picard.PoincareBundle.Tensor.LineBundles.tensor L L) x)
      (Picard.PoincareBundle.Subgroup.TranslationFibers.transportIso i (Picard.PoincareBundle.Tensor.LineBundles.tensor L L) (tensorTranslation i L t) x y a hx ≪≫
        Picard.PoincareBundle.Subgroup.TranslationFibers.transportIso i (Picard.PoincareBundle.Tensor.LineBundles.tensor L L) (tensorTranslation i L t) y z b hy)
      (Picard.PoincareBundle.Subgroup.TranslationFibers.transportIso i (Picard.PoincareBundle.Tensor.LineBundles.tensor L L) (tensorTranslation i L t) x z c hz) =
    Picard.PoincareBundle.Line.IsoRatios.ratio (Picard.PoincareBundle.FiberIsomorphismRatios.fiberLine L x) (e ≪≫ f) g ^ 2
  rw [hc, transportIso_tensorTranslation]
  exact ratio_tensor_square_conjugate (Picard.PoincareBundle.FiberIsomorphismRatios.fiberLine L x)
    (Picard.PoincareBundle.FiberIsomorphismRatios.fiberLine (Picard.PoincareBundle.Tensor.LineBundles.tensor L L) x)
    (fiberTensorIso L x) (fiberTensorIso L z) (e ≪≫ f) g

theorem productDefect_tensorTranslation [GrpObj H] [IsCommMonObj H] [IsMonHom i]
    {T : Over S} (a b : T ⟶ H) (x : T ⟶ A) :
    Picard.PoincareBundle.Subgroup.ProductDefect.value i (Picard.PoincareBundle.Tensor.LineBundles.tensor L L)
      (tensorTranslation i L t) a b x = Picard.PoincareBundle.Subgroup.ProductDefect.value i L t a b x ^ 2 :=
  defect_tensorTranslation i L t x ((a ≫ i) * x) (((a * b) ≫ i) * x)
    a b (a * b) rfl (Picard.PoincareBundle.Subgroup.ProductDefect.translate_mul i a b x) rfl
end Defects

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H A : Over (Spec (.of k))} [GrpObj H] [IsCommMonObj H] [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]
  (i : H ⟶ A) [IsMonHom i] (L : Picard.PoincareBundle.Line.Bundles.LineBundle A.left)
  (t : Picard.PoincareBundle.Line.Fibers.fiber L (snd H A) ≅ Picard.PoincareBundle.Line.Fibers.fiber L (Picard.PoincareBundle.NormalizedKernelTranslation.action i))

theorem value_tensorTranslation {T : Over (Spec (.of k))} (a b : T ⟶ H) :
    Picard.PoincareBundle.Subgroup.DefectParameters.value i (Picard.PoincareBundle.Tensor.LineBundles.tensor L L)
      (tensorTranslation i L t) a b = Picard.PoincareBundle.Subgroup.DefectParameters.value i L t a b ^ 2 := by
  calc
    _ = Picard.PoincareBundle.Subgroup.ProductDefect.value i (Picard.PoincareBundle.Tensor.LineBundles.tensor L L)
        (tensorTranslation i L t) a b (1 : T ⟶ A) :=
      (Picard.PoincareBundle.Subgroup.DefectParameters.defect_eq_value i (Picard.PoincareBundle.Tensor.LineBundles.tensor L L)
        (tensorTranslation i L t) a b (1 : T ⟶ A)).symm
    _ = Picard.PoincareBundle.Subgroup.ProductDefect.value i L t a b (1 : T ⟶ A) ^ 2 :=
      productDefect_tensorTranslation i L t a b (1 : T ⟶ A)
    _ = _ := congrArg (fun z => z ^ 2)
      (Picard.PoincareBundle.Subgroup.DefectParameters.defect_eq_value i L t a b (1 : T ⟶ A))

theorem normalized_tensorTranslation_symmetric {T : Over (Spec (.of k))}
    (a b : T ⟶ H) (ha : a * a = 1) :
    Picard.PoincareBundle.Subgroup.DefectParameters.value i (Picard.PoincareBundle.Tensor.LineBundles.tensor L L)
      (tensorTranslation i L (Picard.PoincareBundle.NormalizedTranslationUnit.translation i L t)) a b =
    Picard.PoincareBundle.Subgroup.DefectParameters.value i (Picard.PoincareBundle.Tensor.LineBundles.tensor L L)
      (tensorTranslation i L (Picard.PoincareBundle.NormalizedTranslationUnit.translation i L t)) b a := by
  let t₀ := Picard.PoincareBundle.NormalizedTranslationUnit.translation i L t
  change Picard.PoincareBundle.Subgroup.DefectParameters.value i (Picard.PoincareBundle.Tensor.LineBundles.tensor L L)
      (tensorTranslation i L t₀) a b =
    Picard.PoincareBundle.Subgroup.DefectParameters.value i (Picard.PoincareBundle.Tensor.LineBundles.tensor L L)
      (tensorTranslation i L t₀) b a
  calc
    _ = Picard.PoincareBundle.Subgroup.DefectParameters.value i L t₀ a b ^ 2 :=
      value_tensorTranslation i L t₀ a b
    _ = Picard.PoincareBundle.Subgroup.DefectParameters.value i L t₀ b a ^ 2 :=
      CocycleSquareSymmetry.cocycle_square_symmetric_of_involution
        (fun x y : T ⟶ H => Picard.PoincareBundle.Subgroup.DefectParameters.value i L t₀ x y)
        (fun x => Picard.PoincareBundle.NormalizedDefectUnitLaws.one_left i L t x)
        (fun x => Picard.PoincareBundle.NormalizedDefectUnitLaws.one_right i L t x)
        (fun x y z => Picard.PoincareBundle.Subgroup.DefectCocycle.cocycle i L t₀ x y z) a b ha
    _ = _ := (value_tensorTranslation i L t₀ b a).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LineTranslation.PoincareBundle
