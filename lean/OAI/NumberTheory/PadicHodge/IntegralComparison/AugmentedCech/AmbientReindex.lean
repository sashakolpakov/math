import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.AmbientTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindexTotal

/-! # Ambient Reindex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.AmbientReindex

noncomputable section

/-! The original ambient-open coordinates commute with an actual
finite-product-preserving change of the principal index category. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {X : TopCat.{u}} {C D : Type u}
  [Preorder C] [HasFiniteProducts C] [Preorder D] [HasFiniteProducts D]
  (r : C ⥤ D) [PreservesFiniteProducts r] (F : D ⥤ Opens X)
  {ι : Type u} [LinearOrder ι] (W : ι → C)
  [hF : ∀ (n : ℕ) (a : Fin (n+1) → ι),
    PreservesLimit (Discrete.functor ((r.obj ∘ W) ∘ a)) F]

instance composite_tuple (n : ℕ) (a : Fin (n+1) → ι) :
    PreservesLimit (Discrete.functor (W ∘ a)) (r ⋙ F) := by
  let : PreservesLimit (Discrete.functor (r.obj ∘ (W ∘ a))) F := hF n a
  let : PreservesLimit (Discrete.functor (W ∘ a) ⋙ r) F :=
    preservesLimit_of_iso_diagram F (Discrete.compNatIsoDiscrete (W ∘ a) r).symm
  infer_instance

def terminalIso : F.obj (r.obj (⊤_ C)) ≅ F.obj (⊤_ D) :=
  F.mapIso (PreservesTerminal.iso r)

theorem terminal_eq : F.obj (r.obj (⊤_ C)) = F.obj (⊤_ D) :=
  le_antisymm (leOfHom (terminalIso r F).hom) (leOfHom (terminalIso r F).inv)

variable {A : Type v} [Category A] [Preadditive A] [HasProducts.{u} A]

omit [Preadditive A] in
private theorem transport_π (P : (Opens X)ᵒᵖ ⥤ A) (V : ι → Opens X)
    {U₁ U₂ : Opens X} (h : U₁ = U₂) (n : ℕ) (a : AugmentedOrdered.Cech.Index ι n) :
    eqToHom (congrArg (fun U => AugmentedOrdered.Cech.object V ((RelativeCech.Intersections.intersect U).op ⋙ P) n) h) ≫
      Pi.π (fun b : AugmentedOrdered.Cech.Index ι n => P.obj (op (U₂ ⊓ (AugmentedOrdered.Cech.formal V n).obj b))) a =
    Pi.π (fun b : AugmentedOrdered.Cech.Index ι n => P.obj (op (U₁ ⊓ (AugmentedOrdered.Cech.formal V n).obj b))) a ≫
      P.map (eqToHom (congrArg (fun U => op (U ⊓ (AugmentedOrdered.Cech.formal V n).obj a)) h)) := by
  subst U₂
  change 𝟙 _ ≫ _ = _ ≫ P.map (𝟙 _)
  rw [P.map_id, Category.id_comp, Category.comp_id]

omit [Preadditive A] in
theorem component (P : (Opens X)ᵒᵖ ⥤ A) (n : ℕ) :
    (AugmentedOrdered.CechReindex.componentIso r W (F.op ⋙ P) n).hom ≫
      (AmbientCoordinates.componentIso F (r.obj ∘ W) P n).hom =
    (AmbientCoordinates.componentIso (r ⋙ F) W P n).hom ≫
      eqToHom (congrArg (fun U => AugmentedOrdered.Cech.object (F.obj ∘ r.obj ∘ W)
        ((RelativeCech.Intersections.intersect U).op ⋙ P) n) (terminal_eq r F)) := by
  apply Pi.hom_ext
  intro a
  change AugmentedOrdered.Cech.Index ι n at a
  erw [Category.assoc, AmbientCoordinates.component_hom_π,
    ← Category.assoc, AugmentedOrdered.CechReindex.component_hom_π]
  simp only [Category.assoc]
  erw [transport_π P (F.obj ∘ r.obj ∘ W) (terminal_eq r F) n a]
  simp only [← Category.assoc]
  erw [AmbientCoordinates.component_hom_π]
  simp only [Functor.comp_map, Functor.op_map, Category.assoc]
  congr 1
  rw [← P.map_comp, ← P.map_comp]
  congr 1

theorem complex (P : (Opens X)ᵒᵖ ⥤ A) :
    (AugmentedOrdered.CechReindex.iso r W (F.op ⋙ P)).hom ≫
      (AmbientCoordinates.iso F (r.obj ∘ W) P).hom =
    (AmbientCoordinates.iso (r ⋙ F) W P).hom ≫
      eqToHom (congrArg (fun U => AugmentedOrdered.Cech.complex (F.obj ∘ r.obj ∘ W)
        ((RelativeCech.Intersections.intersect U).op ⋙ P)) (terminal_eq r F)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  simpa only [comp_f, eqToHom_f, AugmentedOrdered.CechReindex.iso,
    AmbientCoordinates.iso, HomologicalComplex.Hom.isoOfComponents] using
      component r F W P n

variable (K : CochainComplex ((Opens X)ᵒᵖ ⥤ A) ℕ)

abbrev restricted := ((AmbientTotal.restriction F).mapHomologicalComplex (.up ℕ)).obj K

def bicomplexTransport :
    RelativeCech.Total.source (F.obj (r.obj (⊤_ C))) (F.obj ∘ r.obj ∘ W) K ≅
      RelativeCech.Total.source (F.obj (⊤_ D)) (F.obj ∘ r.obj ∘ W) K :=
  eqToIso (congrArg (fun U => RelativeCech.Total.source U (F.obj ∘ r.obj ∘ W) K)
    (terminal_eq r F))

theorem bicomplex :
    (AugmentedOrdered.CechReindexTotal.bicomplexIso r W (restricted F K)).hom ≫
      (AmbientTotal.bicomplexIso F (r.obj ∘ W) K).hom =
    (AmbientTotal.bicomplexIso (r ⋙ F) W K).hom ≫
      (bicomplexTransport r F W K).hom := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [comp_f, bicomplexTransport, eqToIso.hom, eqToHom_f]
  convert component r F W (K.X q) n using 1 <;> rfl

variable [HasCoproducts.{0} A]

def totalTransport := HomologicalComplex₂.total.mapIso (bicomplexTransport r F W K) (.up ℕ)

theorem total :
    (AugmentedOrdered.CechReindexTotal.totalIso r W (restricted F K)).hom ≫
      (AmbientTotal.totalIso F (r.obj ∘ W) K).hom =
    (AmbientTotal.totalIso (r ⋙ F) W K).hom ≫
      (totalTransport r F W K).hom := by
  let T := HomologicalComplex₂.totalFunctor A (.up ℕ) (.up ℕ) (.up ℕ)
  exact (T.map_comp _ _).symm.trans
    ((congrArg T.map (bicomplex r F W K)).trans (T.map_comp _ _))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.AmbientReindex
