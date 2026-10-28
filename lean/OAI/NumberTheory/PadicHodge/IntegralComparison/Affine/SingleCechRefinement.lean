import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.OrderedInjective
import OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.OrderedCoverRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.AugmentedCechRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.RefinementProductReflect
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.RefinementQuasiIso

/-! # Single Cech Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.SingleCechRefinement

noncomputable section

/-! Affine refinements act by the actual original maps on a single
quasicoherent sheaf, in the same presheaf coordinates as its chosen
injective resolution. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem square_isIso {D : Type*} [Category D] {A B C E : D}
    (a : A ⟶ B) (b : C ⟶ E) (e : A ⟶ C) (f : B ⟶ E)
    [IsIso a] [IsIso e] [IsIso f] (h : e ≫ b = a ≫ f) : IsIso b := by
  have hb : b = inv e ≫ a ≫ f := by
    apply (cancel_epi e).mp
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using h
  rw [hb]
  infer_instance

universe u
variable {X : Scheme.{u}} [X.IsSeparated]
  (A : X.Opens) (hA : IsAffineOpen A)
  {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (U : ι → X.Opens) (V : κ → X.Opens)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  (O : X.Opens)
  (hU : iSup (fun j => A ⊓ U j) = O) (hV : iSup (fun j => A ⊓ V j) = O)
  (haU : ∀ j, IsAffineOpen (U j)) (haV : ∀ j, IsAffineOpen (V j))

include hA O hU hV haU haV in
omit [LinearOrder ι] [LinearOrder κ] in
theorem relative_row (M : X.Modules) [M.IsQuasicoherent] :
    QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r
      (RelativeCech.Intersections.presheaf A M.presheaf)) := by
  let F := RelativeCech.Intersections.intersect A
  let : ∀ (n : ℕ) (a : Fin (n+1) → ι), PreservesLimit (Discrete.functor (U ∘ a)) F :=
    fun _ _ => RelativeCech.RefinementQuasiIso.intersection_preserves_product A _
  let : ∀ (n : ℕ) (a : Fin (n+1) → κ), PreservesLimit (Discrete.functor (V ∘ a)) F :=
    fun _ _ => RelativeCech.RefinementQuasiIso.intersection_preserves_product A _
  let : QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map (F.obj ∘ U) (F.obj ∘ V)
      (Cech.RefinementProductCoordinates.mappedCover F U V r) M.presheaf) :=
    Open.CoverRefinementQuasiIso.Cech.quasiIso (F.obj ∘ U) (F.obj ∘ V)
      (Cech.RefinementProductCoordinates.mappedCover F U V r) M O hU hV
      (fun j => hA.inf (haU j)) (fun j => hA.inf (haV j))
  exact Cech.RefinementProductReflect.Coordinates.reflect F U V r M.presheaf

include hA O hU hV haU haV in
theorem relative_complex (K : CochainComplex X.Modules ℕ)
    [∀ q, (K.X q).IsQuasicoherent] :
    QuasiIso (RelativeCech.Refinement.map A U V r (Relative.AdditiveCechConcentration.coefficients K)) :=
  Additive.AugmentedCechRefinement.total_quasiIso U V r _
    (fun q => relative_row A hA U V r O hU hV haU haV (K.X q))

variable (N : X.Modules) (c : ℕ)

def coefficientsIso : Relative.AdditiveCechConcentration.coefficients ((single X.Modules (.up ℕ) c).obj N) ≅
    OrderedInjective.Comparison.sourcePresheaf N c :=
  ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex
    (.up ℕ)).mapIso
      ((singleMapHomologicalComplex (SheafOfModules.toSheaf X.ringCatSheaf) (.up ℕ) c).app N)

omit [X.IsSeparated] in
private theorem relative_map_isIso {K L : CochainComplex (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ}
    (a : K ⟶ L) [IsIso a] (q : ℕ) :
    IsIso (homologyMap (RelativeCech.Total.sourceMap A U a) q) := by
  change IsIso ((((RelativeCech.Total.localFunctor A U).mapHomologicalComplex (.up ℕ)) ⋙
    HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (.up ℕ) (.up ℕ) (.up ℕ) ⋙
      homologyFunctor AddCommGrpCat.{u} (.up ℕ) q).map a)
  infer_instance

variable [N.IsQuasicoherent]

include hA O hU hV haU haV in
theorem relative (q : ℕ) : IsIso (RelativeCech.Refinement.homology A U V r
    (OrderedInjective.Comparison.sourcePresheaf N c) q) := by
  let : ∀ k, (((single X.Modules (.up ℕ) c).obj N).X k).IsQuasicoherent :=
    QuasicoherentTruncation.single N c
  let := relative_complex A hA U V r O hU hV haU haV ((single X.Modules (.up ℕ) c).obj N)
  let : IsIso (RelativeCech.Refinement.homology A U V r
      (Relative.AdditiveCechConcentration.coefficients ((single X.Modules (.up ℕ) c).obj N)) q) := by
    change IsIso (homologyMap (RelativeCech.Refinement.map A U V r
      (Relative.AdditiveCechConcentration.coefficients ((single X.Modules (.up ℕ) c).obj N))) q)
    infer_instance
  let := relative_map_isIso A U (coefficientsIso N c).hom q
  let := relative_map_isIso A V (coefficientsIso N c).hom q
  exact square_isIso _ _ _ _
    (RelativeCech.Refinement.homology_naturality A U V r (coefficientsIso N c).hom q)

include haU haV in
theorem ordered (hUt : iSup U = ⊤) (hVt : iSup V = ⊤) (q : ℕ) :
    IsIso (homologyMap (OrderedCech.Refinement.totalMap U V r
      (OrderedInjective.Comparison.sourcePresheaf N c)) q) := by
  let : ∀ k, (((single X.Modules (.up ℕ) c).obj N).X k).IsQuasicoherent :=
    QuasicoherentTruncation.single N c
  let := Additive.OrderedCoverRefinement.quasiIso U V r hUt hVt haU haV
    ((single X.Modules (.up ℕ) c).obj N)
  let : IsIso (homologyMap ((Presheaf.OrderedCover.Comparison.totalFunctor U).map
      (coefficientsIso N c).hom) q) := by
    change IsIso (((Presheaf.OrderedCover.Comparison.totalFunctor U) ⋙
      homologyFunctor AddCommGrpCat.{u} (.up ℕ) q).map (coefficientsIso N c).hom)
    infer_instance
  let : IsIso (homologyMap ((Presheaf.OrderedCover.Comparison.totalFunctor V).map
      (coefficientsIso N c).hom) q) := by
    change IsIso (((Presheaf.OrderedCover.Comparison.totalFunctor V) ⋙
      homologyFunctor AddCommGrpCat.{u} (.up ℕ) q).map (coefficientsIso N c).hom)
    infer_instance
  exact square_isIso _ _ _ _
    (Presheaf.OrderedCover.Comparison.homology_naturality U V r (coefficientsIso N c).hom q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.SingleCechRefinement
