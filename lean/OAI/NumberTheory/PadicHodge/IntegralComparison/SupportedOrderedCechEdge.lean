import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsExcision
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechZero
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechFunctor

/-! # Supported Ordered Cech Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SupportedOrderedCechEdge.Abelian

noncomputable section

/-! The canonical supported-section augmentation into the actual
augmented ordered Čech total of an abelian-category-valued sheaf complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem compose_inverse_square {D : Type*} [Category* D]
    {N₁ N₂ C₁ C₂ T₁ T₂ : D}
    (s : N₁ ⟶ N₂) (a : N₁ ⟶ C₁) (b : N₂ ⟶ C₂) (d : C₁ ⟶ C₂)
    (e₁ : T₁ ≅ C₁) (e₂ : T₂ ≅ C₂) (m : T₁ ⟶ T₂)
    (h₁ : s ≫ b = a ≫ d) (h₂ : m ≫ e₂.hom = e₁.hom ≫ d) :
    s ≫ b ≫ e₂.inv = a ≫ e₁.inv ≫ m := by
  apply (cancel_mono e₂.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h₂, ← Category.assoc e₁.inv e₁.hom d, e₁.inv_hom_id, Category.id_comp]
  exact h₁

universe u
variable (D : Type (u+1)) [Category.{u} D] [Abelian D] [HasLimitsOfSize.{u,u} D]
  (X : TopCat.{u}) {C : Type u} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X) {ι : Type u} [LinearOrder ι] (U : ι → C) (O : Opens X)

local notation "V" => F.obj (⊤_ C)

def supportFunctor :
    Sheaf (Opens.grothendieckTopology X) D ⥤
      D :=
  Supported.SectionsExcision.supported V (V ⊓ O) inf_le_left

instance supportFunctor_additive : (supportFunctor D X F O).Additive := by
  dsimp only [supportFunctor]
  infer_instance

def presheaves : Sheaf (Opens.grothendieckTopology X) D ⥤ Cᵒᵖ ⥤ D :=
  sheafToPresheaf (Opens.grothendieckTopology X) D ⋙
    (Functor.whiskeringLeft Cᵒᵖ (Opens X)ᵒᵖ D).obj F.op

instance presheaves_additive : (presheaves D X F).Additive := by
  dsimp only [presheaves]
  infer_instance

variable (K : CochainComplex (Sheaf (Opens.grothendieckTopology X)
  D) ℕ)

def source : CochainComplex D ℕ := ((supportFunctor D X F O).mapHomologicalComplex (.up ℕ)).obj K

def presheafComplex : CochainComplex (Cᵒᵖ ⥤ D) ℕ :=
  ((presheaves D X F).mapHomologicalComplex (.up ℕ)).obj K

def bicomplex : HomologicalComplex₂ D (.up ℕ) (.up ℕ) :=
  AugmentedOrdered.CechFunctor.bicomplex (D := D) U
    (presheafComplex D X F K)

def component (q : ℕ) : (source D X F O K).X q ⟶ ((SupportedOrderedCechEdge.Abelian.bicomplex D X F U K).X q).X 0 :=
  (Supported.SectionsExcision.inclusion V (V ⊓ O) inf_le_left).app (K.X q) ≫
    (AugmentedOrdered.CechZero.zeroIso (D := D) U (F.op ⋙ (K.X q).obj)).inv

theorem comm (q q' : ℕ) :
    component D X F U O K q ≫ ((SupportedOrderedCechEdge.Abelian.bicomplex D X F U K).d q q').f 0 =
      (source D X F O K).d q q' ≫ component D X F U O K q' := by
  let f : F.op ⋙ (K.X q).obj ⟶ F.op ⋙ (K.X q').obj :=
    Functor.whiskerLeft F.op (K.d q q').hom
  have hd : ((SupportedOrderedCechEdge.Abelian.bicomplex D X F U K).d q q').f 0 =
      AugmentedOrdered.CechFunctor.objectMap U f 0 := by rfl
  have hs : (source D X F O K).d q q' = (supportFunctor D X F O).map (K.d q q') := by rfl
  rw [hd, hs]
  simpa only [component, Category.assoc] using (compose_inverse_square (D := D)
    ((supportFunctor D X F O).map (K.d q q'))
    ((Supported.SectionsExcision.inclusion V (V ⊓ O) inf_le_left).app (K.X q))
    ((Supported.SectionsExcision.inclusion V (V ⊓ O) inf_le_left).app (K.X q'))
    ((Supported.SectionsExcision.sections V).map (K.d q q'))
    (AugmentedOrdered.CechZero.zeroIso (D := D) U (F.op ⋙ (K.X q).obj))
    (AugmentedOrdered.CechZero.zeroIso (D := D) U (F.op ⋙ (K.X q').obj))
    (AugmentedOrdered.CechFunctor.objectMap (D := D) U f 0)
    ((Supported.SectionsExcision.inclusion V (V ⊓ O) inf_le_left).naturality (K.d q q'))
    (AugmentedOrdered.CechZero.zeroIso_naturality (D := D)
      (Q := F.op ⋙ (K.X q').obj) U (F.op ⋙ (K.X q).obj) f)).symm

variable (hO : ∀ i, F.obj (U i) ≤ O)

include hO in
theorem cocycle (q : ℕ) :
    component D X F U O K q ≫ ((SupportedOrderedCechEdge.Abelian.bicomplex D X F U K).X q).d 0 1 = 0 := by
  change component D X F U O K q ≫
    (AugmentedOrdered.Cech.complex U (F.op ⋙ (K.X q).obj)).d 0 1 = 0
  have hd : (AugmentedOrdered.Cech.complex U (F.op ⋙ (K.X q).obj)).d 0 1 =
      AugmentedOrdered.Cech.differential U (F.op ⋙ (K.X q).obj) 0 :=
    CochainComplex.of_d (AugmentedOrdered.Cech.object U (F.op ⋙ (K.X q).obj))
      (AugmentedOrdered.Cech.differential U (F.op ⋙ (K.X q).obj)) 0
  rw [hd]
  apply Pi.hom_ext
  intro a
  rw [zero_comp, Category.assoc]
  change ((Supported.SectionsExcision.inclusion V (V ⊓ O) inf_le_left).app (K.X q) ≫
    (AugmentedOrdered.CechZero.zeroIso (D := D) U (F.op ⋙ (K.X q).obj)).inv) ≫
      AugmentedOrdered.Cech.differential U (F.op ⋙ (K.X q).obj) 0 ≫
        Pi.π (fun b : AugmentedOrdered.Cech.Index ι 1 =>
          (F.op ⋙ (K.X q).obj).obj (op ((AugmentedOrdered.Cech.formal U 1).obj b))) a = 0
  rw [Category.assoc, AugmentedOrdered.CechZero.zeroIso_inv_differential_π]
  let T := (AugmentedOrdered.Cech.formal U 1).obj a
  have hT : F.obj T ≤ V ⊓ O :=
    le_inf (leOfHom (F.map (terminal.from T)))
      ((leOfHom (F.map (Pi.π (fun i : Fin 1 => U (a.val i)) 0))).trans (hO (a.val 0)))
  have he : F.map (terminal.from T) =
      (homOfLE hT : F.obj T ⟶ V ⊓ O) ≫ homOfLE inf_le_left := Subsingleton.elim _ _
  change kernel.ι ((Supported.SectionsExcision.restriction V (V ⊓ O) inf_le_left).app (K.X q)) ≫
    (K.X q).obj.map (F.map (terminal.from T)).op = 0
  rw [he, op_comp, Functor.map_comp, ← Category.assoc]
  exact (congrArg (fun a => a ≫ (K.X q).obj.map (homOfLE hT).op)
    (kernel.condition ((Supported.SectionsExcision.restriction V (V ⊓ O) inf_le_left).app
      (K.X q)))).trans zero_comp

local instance total_exists : (SupportedOrderedCechEdge.Abelian.bicomplex D X F U K).HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts _

def map : source D X F O K ⟶ (SupportedOrderedCechEdge.Abelian.bicomplex D X F U K).total (.up ℕ) :=
  (AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge (bicomplex D X F U K)) (source D X F O K)
    (component D X F U O K) (fun q q' _ => comm D X F U O K q q')
    (cocycle D X F U O K hO)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SupportedOrderedCechEdge.Abelian
